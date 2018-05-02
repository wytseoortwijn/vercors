var bodyparser = require('body-parser');
var express = require('express');
var fs = require('fs');
var http = require('http');
var path = require('path');
var ratelimiter = require('express-rate-limit');
var syncexec = require('sync-exec');
var temp = require('temp');

var memorystore = require('./memory-store');

var app = express();

// automatically track and cleanup temporary files
temp.track();

// Rise4fun indicates that their requests are GZIP encoded, but they are not actually encoded.
// To prevent the bodyparser to automatically decode the non-encoded requests, we remove the encoding entry from the header.
app.use(function (req, res, next) {
	delete req.headers["content-encoding"];
	next();
});

// enable json and set the assets directory
app.use(express.static('public'));
app.use(bodyparser.json());

var store = new memorystore();

// to prevent denial-of-service attacks, construct a rate limit for each incoming verification request
var limiter = new ratelimiter({
  windowMs: 30 * 1000, // 30 seconds
  max: 1, // limit each 1 requests per windowMs (per IP)
  delayMs: 0, // disable delaying - full speed until the max limit is reached
	keyGenerator: function (req) {
		return 'all';
	},
	message: JSON.stringify({
		Version: '1.0',
		Outputs: [{ MimeType: 'text/plain', Value: 'The verification server is currently too busy (try again in 20 seconds)...' }]
	}),
	store: store
});

app.use(limiter);

app.get('/', function (req, res) {
  res.send('Hi there! This is the VerCors interface for Rise4fun')
});

// returns standard (generic) Rise4fun metadata 
standard_metadata = function (req) {
	return {
		Name: 'vercors',
		DisplayName: 'Vercors',
		Version: '1.0',
		Email: 'w.h.m.oortwijn@utwente.nl',
		SupportEmail: 'w.h.m.oortwijn@utwente.nl',
		TermsOfUseUrl: 'http://utwente.nl/vercors?terms',
		PrivacyUrl: 'http://utwente.nl/vercors?privacy',
		Institution: 'University of Twente',
		InstitutionUrl: 'http://utwente.nl',
		InstitutionImageUrl: req.protocol + '://' + req.header('host') + '/fmt.png',
		MimeType: 'text/plain',
		SupportsLanguageSyntax: false,
		Title: 'VerCors Verification Toolset',
		Description: 'Verifies memory safety and functional correctness of parallel and concurrent programs.',
		Question: 'Is this program functionally correct?',
		Url: 'http://utwente.nl/vercors',
		VideoUrl: null,
		DisableErrorTable: false,
		Samples: null,
		Tutorials: null
	};
}

// creates a 'servicetoolrequest' JSON object for the provided example file
load_example = function (name, filepath) {
	var fullpath = path.join(__dirname, filepath);
	return { Name: name, Source: fs.readFileSync(fullpath, 'utf8') };
}

// fetch the example program for the specified language (e.g. java, pvl, c) by querying the Vercors tool
fetch_examples = function (lang) {
	var output = syncexec(path.join(__dirname, '../unix/bin/vct --test=../examples --tool=silicon --lang=' + lang + ' --rise4fun-json --include-suite=rise4fun'));
	return JSON.parse(output.stdout);
}

// adds the given list of examples to the given metadata object
populate_examples = function(metadata, samples) {
	metadata.Samples = [];
	for (var i = 0; i < samples.length; i++) {
		metadata.Samples.push(load_example(samples[i].name, samples[i].path));
	}
}

app.get('/java/metadata', function (req, res) {
	// configure metadata
	var metadata = standard_metadata(req);
	metadata.DisplayName = "Vercors-Java";
	metadata.Question = "Is this Java program functionally correct?";
	metadata.SupportsLanguageSyntax = true;

	// fetch examples from Vercors
	populate_examples(metadata, fetch_examples('java').examples);
	
	// render metadata as JSON
	res.json(metadata);
});

app.get('/pvl/metadata', function (req, res) {
	// configure metadata
	var metadata = standard_metadata(req);
	metadata.DisplayName = "Vercors-PVL";
	metadata.Question = "Is this PVL program functionally correct?";
	metadata.SupportsLanguageSyntax = true;

	// fetch examples from Vercors
	populate_examples(metadata, fetch_examples('pvl').examples);

	// render metadata as JSON
	res.json(metadata);
});

app.get('/c/metadata', function (req, res) {
	// configure metadata
	var metadata = standard_metadata(req);
	metadata.DisplayName = "Vercors-C";
	metadata.Question = "Is this C program functionally correct?";
	metadata.SupportsLanguageSyntax = false;

	// fetch examples from Vercors
	populate_examples(metadata, fetch_examples('c').examples);
	
	// render metadata as JSON
	res.json(metadata);
});

// handles '/run' requests made by Rise4fun by executing VerCors on the received program and sending back a result message.
handle_run_vercors = function (req, res, options) {
	// is the content actually parsed with the built-in JSON parser?
	if (req.body == undefined) {
		res.status(400).send('Error: expecting JSON content');
		return;
	}
	
	// does the parsed JSON object has the right format?
	if (req.body.Version == undefined || req.body.Source == undefined) {
		res.status(400).send('Error: incorrect JSON content');
		return;
	}
	
	console.log('INFO - connection accepted')

	// create a temporary file for the received program
	temp.open({ prefix: 'vercors-rise4fun', suffix: options.suffix }, function (err, info) {
		if (err) {
			res.status(400).send('Error: could not create a temporary file');
			console.log(err);
			return;
		}
		
		// close the file descriptor (directly writing with 'fs.write(info.fd, ...)' seems to be buggy.)
		fs.close(info.fd, function (err) {
			if (err) {
				res.status(400).send('Error: could not close the temporary file');
				console.log(err);
				return;
			}
			
			// write the received code to the temp file
			fs.writeFile(info.path, req.body.Source, function (err) {
				if (err) {
					res.status(400).send('Error: could not write to temporary file');
					console.log(err);
					return;
				}
				
				try {
					// execute vercors on the received program (with silicon)
					var toolpath = path.join(__dirname, '../unix/bin/vct --silicon');
					var tooloutput = syncexec(toolpath + ' ' + info.path, 30 * 1000); // timeout: 30 seconds
					var output = tooloutput.stdout;
				
					if (output == '') {
						output = 'Timeout!';
					}
									
					// render the output message as JSON
					res.setHeader('Content-Type', 'application/json');
					res.json({
						Version: "1.0",
						Outputs: [{ MimeType: "text/plain", Value: output }]
					});
				}
				catch (ex) {
					res.setHeader('Content-Type', 'application/json');
					res.json({
						Version: "1.0",
						Outputs: [{ MimeType: "text/plain", Value: 'Timeout!' }]
					});
				}
				finally {
					setTimeout(function () {
						store.resetAll();
					}, 1000);
				}
			});
		});
	});
}

app.post('/java/run', function (req, res) {
	handle_run_vercors(req, res, { suffix: '.java' });
});

app.post('/pvl/run', function (req, res) {
	handle_run_vercors(req, res, { suffix: '.pvl' });
});

app.post('/c/run', function (req, res) {
	handle_run_vercors(req, res, { suffix: '.c' });
});

app.get('/java/language', function (req, res) {
	res.sendFile(path.join(__dirname, '/lang/java.json'));
});

app.get('/pvl/language', function (req, res) {
	res.sendFile(path.join(__dirname, '/lang/pvl.json'));
});

app.use(function (err, req, res, next) {
  console.error(err.stack)
  res.status(500).send('Something broke!')
})

var server = http.createServer(app, "localhost", 1);

server.listen(8080, function () {
	console.log('vercors-rise4fun interface is active and listening on port 8080')
});
