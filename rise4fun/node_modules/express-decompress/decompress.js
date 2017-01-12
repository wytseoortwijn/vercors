/*jshint strict:false node:true */

var eventsToIntercept = ['data', 'end'];
var zlib = require('zlib');
var EventEmitter = require('events').EventEmitter;
var StringDecoder = require('string_decoder').StringDecoder;

var encodings = {
    'gzip': function() {return zlib.createGunzip();},
    'deflate': function() {return zlib.createDeflate();}
};

module.exports = {
    create: function() {
        return function decompress(req, res, next) {

            var contentEncoding = req.headers["content-encoding"];
            var isCompressedRequest = encodings.hasOwnProperty(contentEncoding);
            
            if(!isCompressedRequest) {
                return next();
            }

            //create the decompression stream with zlib for the encoding
            var decompressStream = encodings[contentEncoding]();
            //forward the request stream to the decompression stream
            req.pipe(decompressStream);
            //hold on to the original req.on
            var originalOn = req.on.bind(req);

            //since zlib streams don't support setEncoding, we need to intercept
            //the data and end events. This way we can pass the buffers emited by
            //the decompression stream through a string decoder to emit strings
            var interceptEmitter = new EventEmitter();
            var stringDecoder;
            function onInterceptedEvent(eventName, buffer) {
                var chunk = buffer;
                if(buffer && stringDecoder) {
                    chunk = stringDecoder.write(buffer);
                }
                //emit events to listeners of data and end event on request
                interceptEmitter.emit(eventName, chunk);
            }
            //attach listeners to decompression stream
            eventsToIntercept.forEach(function(eventName) {
                decompressStream.on(eventName, onInterceptedEvent.bind(null, eventName));
            });

            //replace request.on so we can intercept data and end listeners
            req.on = function(eventName, callback) {
                //if we want to intercept this event, attach it to the local event emitter
                if(eventsToIntercept.indexOf(eventName) !== -1) {
                    interceptEmitter.on(eventName, callback);
                } else {
                    originalOn(eventName, callback);
                }
            };
            //create a string decoder that will be used by onInterceptedEvent
            req.setEncoding = function(encoding) {
                stringDecoder = new StringDecoder(encoding);
            };

            return next();
        };
    }
};