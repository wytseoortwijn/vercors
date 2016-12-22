package models

import play.api.libs.json._

/**
 * The documentation of the fields in this class are taken from {@url http://rise4fun.com/dev}.
 */
class ServicetoolSample {
  def this(name:String, source:String) = {
    this()
    this.name = name
    this.source = source
  }
  
  /** gets the name of the sample */
  var name = ""
  
  /** gets the full source of the sample */
  var source = ""
}

object ServicetoolSample {
  /** Converts an {@code ServicetoolSample} instance to JSON. */
  implicit val servicetoolSampleWrites = new Writes[ServicetoolSample] {
    def writes(sample:ServicetoolSample) = Json.obj(
      "Name" -> sample.name,
      "Source" -> sample.source
    )
  }
}