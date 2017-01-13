var bodyparser = require('body-parser');
var express = require('express');
var fs = require('fs');
var path = require('path');
var syncexec = require('sync-exec');
var temp = require('temp');
var app = express();

// automatically track and cleanup temporary files
temp.track();

// Rise4fun claims to encode their content using GZIP, but it appears that the content is not encoded at all!
// to prevent the bodyparser to automatically decode the apparently non-encoded contents, we remove the encoding entry from the header.
app.use(function (req, res, next) {
	delete req.headers["content-encoding"];
	next();
});

// enable json and set the assets directory
app.use(express.static('public'));
app.use(bodyparser.json());

app.get('/', function (req, res) {
  res.send('Hi there! This is the Vercors interface for Rise4fun')
});

// returns standard (generic) Rise4fun metadata 
standard_metadata = function (req) {
	return {
		Name: 'vercors',
		DisplayName: 'VerCors',
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
	var fullpath = path.join(__dirname, '../examples/', filepath);
	return { Name: name, Source: fs.readFileSync(fullpath, 'utf8') };
}

app.get('/java/metadata', function (req, res) {
	// configure metadata
	var metadata = standard_metadata(req);
	metadata.DisplayName = "VerCors-Java";
	metadata.Question = "Is this Java program functionally correct?";
	metadata.SupportsLanguageSyntax = true;

	// populate with sample programs
	metadata.Samples = [
		load_example("BasicAssert.java", "basic/BasicAssert.java")
	];
	
	// render metadata as JSON
	res.json(metadata);
});

app.get('/pvl/metadata', function (req, res) {
	// configure metadata
	var metadata = standard_metadata(req);
	metadata.DisplayName = "VerCors-PVL";
	metadata.Question = "Is this PVL program functionally correct?";
	metadata.SupportsLanguageSyntax = false;

	// populate with sample programs
	metadata.Samples = [
		load_example("addvec2.pvl", "openmp/addvec2.pvl")
	];
	
	// render metadata as JSON
	res.json(metadata);
});

app.get('/c/metadata', function (req, res) {
	// configure metadata
	var metadata = standard_metadata(req);
	metadata.DisplayName = "VerCors-C";
	metadata.Question = "Is this C program functionally correct?";
	metadata.SupportsLanguageSyntax = false;

	// populate with sample programs
	metadata.Samples = [
		load_example("zero-spec.c", "openmp/zero-spec.c")
	];
	
	// render metadata as JSON
	res.json(metadata);
});

// this function handles 'run' requests made by Rise4fun: it executes VerCors on the received program and sends back a result message.
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

	// create a temporary file for the received (java) program
	temp.open({ prefix: 'vercors-rise4fun', suffix: options.suffix }, function (err, info) {
		if (err) {
			res.status(400).send('Error: could not create a temporary file');
			console.log(err);
			return;
		}

		// write the program to the temp file
		fs.write(info.fd, req.body.Source);
		fs.close(info.fd, function (err) {
			if (err) {
				res.status(400).send('Error: could not write to temporary file');
				console.log(err);
				return;
			}

			// execute vercors on the received program (with silicon)
			var toolpath = path.join(__dirname, '../unix/bin/vct --silicon');
			var tooloutput = syncexec(toolpath + ' ' + info.path);
			
			// render the output message as JSON
			res.setHeader('Content-Type', 'application/json');
			res.json({
				Version: "1.0",
				Outputs: [{ MimeType: "text/plain", Value: tooloutput.stdout }]
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

// send the Java syntax definition (for syntax highlighting)
app.get('/java/language', function (req, res) {
	res.sendFile(path.join(__dirname, '/lang/java.json'));
});

// start the app!
app.listen(8080, function () {
  console.log('vercors-rise4fun interface active and listening on port 8080')
});
