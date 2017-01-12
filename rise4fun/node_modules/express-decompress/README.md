Supports gzip and deflate compression. Use as follows:
```javascript
app.use(require('express-decompress').create());
```
Add this middleware before the body parser in order to have request.body populated as normal with compressed requests.