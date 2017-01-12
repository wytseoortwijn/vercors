var bodyparser = require('body-parser');
var exec = require('child_process').exec;
var express = require('express');
var fs = require('fs');
var path = require('path');
var temp = require('temp');

var app = express();

// automatically track and cleanup temp files
temp.track();

// rise4fun claims to encode their content using GZIP, but it appears that the content is not encoded at all!
// to prevent the bodyparser to automatically decode the non-encoded contents, we remove the encoding entry from the header.
app.use(function (req, res, next) {
	delete req.headers["content-encoding"];
	next();
});

app.use(express.static('public'));
app.use(bodyparser.json());

app.get('/', function (req, res) {
  res.send('Hi there! This is the Vercors interface for Rise4fun.')
});

app.get('/metadata', function (req, res) {
	// construct a metadata object by filling in the necessary fields
	var data = new Object();
	data.Name = "vercors";
  data.DisplayName = "Vercors";
  data.Version = "1.0";
  data.Email = "w.h.m.oortwijn@utwente.nl";
  data.SupportEmail = "w.h.m.oortwijn@utwente.nl";
  data.TermsOfUseUrl = "http://utwente.nl/vercors?terms";
  data.PrivacyUrl = "http://utwente.nl/vercors?privacy";
  data.Institution = "University of Twente";
  data.InstitutionUrl = "http://utwente.nl";
  data.InstitutionImageUrl = "http://" + req.header('host') + "/fmt.png";
  data.MimeType = "text/plain";
	data.SupportsLanguageSyntax = false;
  data.Title = "Vercors Verification Toolset";
  data.Description = "Verifies memory safety and functional correctness of parallel and concurrent programs.";
  data.Question = "Is this program functionally correct?";
  data.Url = "http://utwente.nl/vercors";
	data.VideoUrl = null;
	data.DisableErrorTable = false;
	data.Tutorials = null;
	
	// populate the sample programs
	data.Samples = [
		{ Name: "Hello World", Source: "This is a test!!!" }
	];
	
	// render the metadata object as JSON
	res.setHeader('Content-Type', 'application/json');
	res.json(data);
});

app.post('/run', function (req, res) {
	// is the content actually parsed with the built-in JSON parser?
	if (req.body == undefined) {
		res.status(400).send('Error: expecting JSON content!');
		return;
	}
	
	// does the parsed JSON object has the right format?
	if (req.body.Version == undefined || req.body.Source == undefined) {
		res.status(400).send('Error: incorrect JSON content!');
		return;
	}
	
	// determine filename and construct its absolute path
	var filename = 'input.java';
	var filepath = path.join(__dirname, '/upload/', filename);

	/*
	// write the received program to the filesystem
	fs.writeFile(filepath, req.body.Source, function (err) {
		if (err) {
			res.status(400).send('Error: could not write the file!');
			console.log(err);
			return;
		}

		exec('nl ' + filepath + ' > ' + filepath + '2', function (error, stdout, stderr) {
			console.log(stdout);
		});
	});
	*/

	temp.open('vercors-rise4fun', function (err, info) {
		if (err) {
			res.status(400).send('Error: could not create a temporary file');
			console.log(err);
			return;
		}

		fs.write(info.fd, req.body.Source);
		fs.close(info.fd, function (err) {
			console.log(info.path);
		});
	});

	// build an output message
	var output = {
		Version: "1.0",
		Outputs: [
			{ MimeType: "text/plain", Value: "ECHO: " + req.body.Source }
		]
	}
	
	// render the output message as JSON
	res.setHeader('Content-Type', 'application/json');
	res.json(output);
});

app.listen(8080, function () {
  console.log('vercors-rise4fun interface active and listening on port 8080.')
});
