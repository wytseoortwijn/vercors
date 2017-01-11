package controllers

import javax.inject._
import play.api._
import play.api.libs.json._
import play.api.mvc._
import models._

@Singleton
class VercorsController @Inject() extends Controller {

  def metadata = Action { request =>
    // construct a metadata object by filling in the necessary fields
    var data = new ServicetoolMetadata()
    data.name = "vercors"
    data.displayname = "Vercors Verification Toolset"
    data.version = "1.0"
    data.email = "w.h.m.oortwijn@utwente.nl"
    data.supportEmail = "w.h.m.oortwijn@utwente.nl"
    data.termsOfUseUrl = "http://utwente.nl/vercors?terms"
    data.privacyUrl = "http://utwente.nl/vercors?privacy"
    data.institution = "University of Twente"
    data.institutionUrl = "http://utwente.nl"
    data.institutionImageUrl = "http://" + request.host + "/assets/images/fmt.png" // there should be a way to automatically generate this URL in a cleaner way..
    data.mimetype = "text/plain"
    data.title = "Vercors Verification Toolset"
    data.description = "Verifies memory safety and functional correctness of parallel and concurrent programs."
    data.question = "Is this program functionally correct?"
    data.url = "http://utwente.nl/vercors"
    
    // populate the metadata object with examples (and, optionally, tutorials)
    data.samples += new ServicetoolSample("Hello World", "Dit is een test")
    
    // render the metadata object as JSON
    Ok(Json.toJson(data))
  }
}