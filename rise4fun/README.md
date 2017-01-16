Vercors Verification Toolset - Rise4fun
===
This directory holds the web interface, written in Node.js, that allows to connect the Vercors toolset to Rise4fun. The current version provides three language front-ends, namely for PVL, Java, and for C. Extending the server to provide more front-ends is straightforward.

Prerequisites
---
- Node.js, which can be downloaded from <https://nodejs.org/> (or be installed by using `apt-get`, e.g. `apt-get install nodejs`).
- NPM, which is the package manager that comes with Node.js (or, alternatively, `apt-get install npm`).

Installation and Deployment
---
1. Clone this repository on your web server: `git clone https://github.com/utwente-fmt/vercors.git`.
2. Install Vercors in the usual way. From the base directory run `./unix/bin/vct-ant`.
3. In the `rise4fun` directory, install all dependencies of our web service by running `npm install`.
4. Start the web service by running `node server.js`.

Implementation
---
The web server exposes three language front-ends as <http://hostname/?lang>, where `?lang` may be `pvl`, `java`, or `c`. Rise4fun communicates via three actions, namely:
- <http://hostname/?lang/metadata>, thereby requesting metadata for the front-end for `?lang` (as a GET request). Internally, this action first runs the command `vct --test=../examples --tool=silicon --lang=?lang --rise4fun-json --include-suite=rise4fun`, which filters out all `?lang` programs in the `./examples` folder that are marked to be exposed for the Rise4fun interface. The `--rise4fun-json` flag indicates that `vct` should print the list of filtered programs as JSON. The web server then fetches the contents of all these programs and builds a metadata response.
- <http://hostname/?lang/run>, thereby sending our web service (in a POST request) a program (written in `.?lang`) that should be verified by the Vercors tool. Internally the `run` action stores the received program as a temporary file, executes `vct --silicon ?tmpfile.?lang` with `?tmpfile` the path of the temporary file, and responds by sending the output of `vct` as a JSON message.
- Optionally, <http://hostname/?lang/language>, which gives a grammar in JSON for `?lang` that is used for syntax highlighting. The grammars are just fetched from the `./lang` directory, that is, taken as `./lang/?lang.json`.

Remark: when Rise4fun calls the `run` action it indicates (in the request header) that the contents are GZIP encoded. However, the contents are not actually encoded. Therefore, `server.js` filters out the `content-encoding` header entries of all requests, for otherwise the JSON body-parser automatically tries to decode the request body and fails, thereby crashing the server.

Exposing Example Programs
---
The web service looks into the `../examples` directory when it is queried for example programs. If you wish to expose a new example program for the language `?lang`, open (or create) a file (with the `.?lang` extension) somewhere in the `../examples` directory and add the comment `//:: suite rise4fun` at the top of the file. The command `vct --test=../examples --tool=silicon --lang=?lang --rise4fun-json --include-suite=rise4fun` prints a JSON string containing the names and paths of all `.?lang` programs in the `../examples` file that have such a comment.
