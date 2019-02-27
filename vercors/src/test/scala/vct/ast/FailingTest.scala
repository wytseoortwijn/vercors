package vct.ast

import org.scalatest._

class FailingTest extends FlatSpec with Matchers {
    "This test" should "deliberately fail" in {
        false should be (true)
    }
}
