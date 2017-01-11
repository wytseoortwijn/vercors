package models

import play.api.libs.json._
import scala.collection.mutable.ArrayBuffer

/**
 * The documentation of the fields in this class are taken from {@url http://rise4fun.com/dev}.
 */
class ServicetoolResponse {
  /** gets the current version of the tool. it should match the version returned by /metadata. */
  var version = ""
  
  /** gets the list of outputs produced by the tool. there should be at least one output of type 'text/plain'. other outputs will be supported in the future. */
  var outputs = new ArrayBuffer[ServicetoolOutput]()
}

object ServicetoolResponse {
  /** Converts an {@code ServicetoolResponse} instance to JSON. */
  implicit val servicetoolResponseWrites = new Writes[ServicetoolResponse] {
    def writes(response:ServicetoolResponse) = Json.obj(
      "Version" -> response.version,
      "Outputs" -> response.outputs
    )
  }
}