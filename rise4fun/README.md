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
