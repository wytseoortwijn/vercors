package models

import play.api.libs.json._
import scala.collection.mutable.ArrayBuffer

/**
 * The documentation of the fields in this class are taken from {@url http://rise4fun.com/dev}.
 */
class ServicetoolMetadata {
  /** gets the short, url-friendly name of the tool. may only contain letters and digits. */
  var name = ""
  
  /** gets the human readable name of the tool. */
  var displayname = ""
  
  /** gets a version number of the form m.n.p.q where m, n, p, q are numbers within the 0, 65535 range. */
  var version = ""
  
  /** gets the email to send outage or administrative email notification. will not be shared with rise4fun users. */
  var email = ""
  
  /** gets the user support email. */
  var supportEmail = ""
  
  /** gets the url pointing to the 'terms of use' [or end user license] document for the tool. */
  var termsOfUseUrl = ""
  
  /** gets the url pointing to the 'privacy' document for the tool. */
  var privacyUrl = ""
  
  /** gets the name of the institution that owns this tool. */
  var institution = ""
  
  /** gets the url pointing to the institution home page. */
  var institutionUrl = ""
  
  /** gets the url pointing to a small logo image of the institution (less than 120px) */
  var institutionImageUrl = ""
  
  /** gets the mime type of the input language. */
  var mimetype = ""
  
  /** indicates if the service supports a custom language definition through the /language end point */
  var supportsLanguageSyntax = false
  
  /** gets a single sentence describing the tool. */
  var title = ""
  
  /** gets a paragraph describing the tool. */
  var description = ""
  
  /** gets the question that the tool can answer, e.g. 'is this program memory safe?' */
  var question = ""
  
  /** gets the url to the tool home page */
  var url = ""
  
  /** (optional) gets the url to a page containing a video about the tool */
  var videourl = ""
  
  /** (optional) disables the parsing of the output to build the error table */
  var disablEerrorTable = false
  
  /** gets the list of samples for the tool, in order. must have at least 1 sample. */
  var samples = new ArrayBuffer[ServicetoolSample]()
}

object ServicetoolMetadata {
  /** Converts an {@code ServicetoolMetadata} instance to JSON. */
  implicit val servicetoolMetadataWrites = new Writes[ServicetoolMetadata] {
    def writes(metadata:ServicetoolMetadata) = Json.obj(
      "Name" -> metadata.name,
      "DisplayName" -> metadata.displayname,
      "Version" -> metadata.version,
      "Email" -> metadata.email,
      "SupportEmail" -> metadata.supportEmail,
      "TermsOfUseUrl" -> metadata.termsOfUseUrl,
      "PrivacyUrl" -> metadata.privacyUrl,
      "Institution" -> metadata.institution,
      "InstitutionUrl" -> metadata.institutionUrl,
      "InstitutionImageUrl" -> metadata.institutionImageUrl,
      "MimeType" -> metadata.mimetype,
      "SupportsLanguageSyntax" -> metadata.supportsLanguageSyntax,
      "Title" -> metadata.title,
      "Description" -> metadata.description,
      "Question" -> metadata.question,
      "Url" -> metadata.url,
      "Samples" -> metadata.samples
    )
  }
}
