package models

import play.api.libs.json._

/**
 * The documentation of the fields in this class are taken from {@url http://rise4fun.com/dev}.
 */
class ServicetoolOutput {
  def this(mimetype:String, value:String) = {
    this()
    this.mimetype = mimetype
    this.value = value
  }
  
  /** gets the mime type of the output */
  var mimetype = ""
  
  /** gets the text of the output */
  var value = ""
}

object ServicetoolOutput {
  /** Converts an {@code ServicetoolOutput} instance to JSON. */
  implicit val servicetoolOutputWrites = new Writes[ServicetoolOutput] {
    def writes(output:ServicetoolOutput) = Json.obj(
      "MimeType" -> output.mimetype,
      "Value" -> output.value
    )
  }
}