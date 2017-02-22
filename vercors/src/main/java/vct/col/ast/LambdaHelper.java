package vct.col.ast;

import java.util.function.Consumer;
import java.util.function.Predicate;
import scala.Function1;
import scala.runtime.AbstractFunction1;
import scala.runtime.BoxedUnit;

/**
 * Collection of methods to convert Java lambdas to Scala lambdas. 
 * @author whmoortwijn
 */
public class LambdaHelper {
	/**
	 * Converts a unary Java lambda procedure (a consumer) `f` to an equivalent
	 * lambda procedure for Scala.
	 * @param f The lambda procedure to convert
	 * @return The converted procedure
	 */
	public static <T> Function1<T,BoxedUnit> fun(Consumer<T> f) {
		return new AbstractFunction1<T,BoxedUnit>() {
			@Override
	    	public BoxedUnit apply(T arg) {
				f.accept(arg);
	    		return BoxedUnit.UNIT;
	    	}
		};
	}
}
