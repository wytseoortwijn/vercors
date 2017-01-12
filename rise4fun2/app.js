var express = require('express')
var app = express()

// directory containing static assets
app.use(express.static('public'))

app.get('/', function (req, res) {
  res.send('Hi there! This is the Vercors REST interface for Rise4fun.')
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
	// build an output message
	var output = {
		Version: "1.0",
		Outputs: [
			{ MimeType: "text/plain", Value: "This is a response!" }
		]
	}
	
	// render the output message as JSON
	res.setHeader('Content-Type', 'application/json');
	res.json(output);
});

app.listen(8080, function () {
  console.log('vercors-rise4fun interface active and listening on port 8080.')
});