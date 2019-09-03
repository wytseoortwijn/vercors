package vct

import sbt._
import Keys._
import java.net.{MalformedURLException, URL, URLConnection, URLStreamHandler, URLStreamHandlerFactory}
import org.apache.ivy.util.CopyProgressEvent
import org.apache.ivy.util.url.{URLHandler, URLHandlerDispatcher, URLHandlerRegistry}

object PatchUrlPlugin extends AutoPlugin {
  class UrlHandler extends URLStreamHandler {
    def openConnection(url: URL): URLConnection = {

      null
    }
  }

  private object UrlHandlerFactory extends URLStreamHandlerFactory {
    override def createURLStreamHandler(proto: String): URLStreamHandler = proto match {
      case "patch" => new UrlHandler;
      case _ => null;
    }
  }

  private class UrlInfo extends org.apache.ivy.util.url.URLHandler.URLInfo(true, 0, 0) {

  }

  class IvyUrlHandler extends org.apache.ivy.util.url.URLHandler {
    def getInternalURL(url: URL): URL = {
      new URL(url.getRef())
    }

    def download(url: java.net.URL, file: java.io.File, progress: org.apache.ivy.util.CopyProgressListener): Unit = {
      val event = new CopyProgressEvent()
      if(progress != null) progress.start(event)
      if(progress != null) progress.end(event)
    }

    def getContentLength(url: java.net.URL, x$2: Int): Long = 0
    def getContentLength(url: java.net.URL): Long = 0
    def getLastModified(url: java.net.URL, x$2: Int): Long = 0
    def getLastModified(url: java.net.URL): Long = 0
    def getURLInfo(url: java.net.URL,x$2: Int): org.apache.ivy.util.url.URLHandler.URLInfo = getURLInfo(url)
    def getURLInfo(url: java.net.URL): org.apache.ivy.util.url.URLHandler.URLInfo = {
      new UrlInfo()
    }
    def isReachable(url: java.net.URL,x$2: Int): Boolean = true
    def isReachable(url: java.net.URL): Boolean = true
    def openStream(url: java.net.URL): java.io.InputStream = null
    def setRequestMethod(x: Int): Unit = {

    }
    def upload(x$1: java.io.File,x$2: java.net.URL,x$3: org.apache.ivy.util.CopyProgressListener): Unit = ???
  }

  override def trigger = allRequirements

  override def projectSettings: Seq[Setting[_]] = Seq(
    onLoad in Global := (onLoad in Global).value andThen { state =>
      // Load the patch URL handler for java.net
      // We may only do this once, so check if it's there by instantiating an example.
      try {
        new URL("patch:example#file:///")
      } catch {
        case _: MalformedURLException =>
          URL.setURLStreamHandlerFactory(UrlHandlerFactory)
      }

      // Load the patch URL handler for ivy
      val dispatcher = URLHandlerRegistry.getDefault match {
        case disp: URLHandlerDispatcher => disp;
        case other => {
          val disp = new URLHandlerDispatcher()
          disp.setDefault(other)
          URLHandlerRegistry.setDefault(disp)
          disp
        };
      }

      dispatcher.setDownloader("patch", new IvyUrlHandler)

      state
    },
  )
}