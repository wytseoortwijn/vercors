package filters

import akka.stream.Materializer
import javax.inject.Inject
import play.api.mvc._
import scala.concurrent.{ExecutionContext, Future}

class DebugFilter @Inject() (implicit val mat: Materializer, ec: ExecutionContext) extends Filter {
  def apply(next: RequestHeader => Future[Result])(request: RequestHeader): Future[Result] = {
    System.out.println("HEADERS:" + request.headers.toString())
    
    next(request).map { result =>
      result
    }
  }
}