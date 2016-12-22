package controllers

import javax.inject._
import play.api._
import play.api.libs.json._
import play.api.mvc._
import models._

@Singleton
class VercorsController @Inject() extends Controller {

  def metadata = Action {
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
    data.institutionImageUrl = "https://fmt.ewi.utwente.nl/redmine/attachments/download/632/UT_Logo_2400_Black_EN.png"
    data.mimetype = "text/x-echo"
    data.title = "Vercors Verification Toolset"
    data.description = "Verifies memory safety and functional correctness of parallel and concurrent programs."
    data.question = "Is this program correct?"
    data.url = "http://utwente.nl/vercors"
    
    // populate the metadata object with examples (and, optionally, tutorials)
    data.samples += new ServicetoolSample("Hello World", "class HelloWorld { }")
    
    // render the metadata object as JSON
    Ok(Json.toJson(data))
  }
}