/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

import com.weiglewilczek.slf4s.Logging
import silver.verifier.PartialVerificationError
import silver.verifier.reasons.{NegativePermission, AssertionFalse}
import interfaces.state.{Store, Heap, PathConditions, State, StateFormatter, ChunkIdentifier}
import interfaces.{Consumer, Evaluator, VerificationResult, Failure}
import interfaces.decider.Decider
import reporting.Bookkeeper
import state.{DirectChunk, DirectFieldChunk, DirectPredicateChunk, DefaultContext}
import state.terms._
import state.terms.perms.{IsNonNegative, IsNoAccess}
import supporters.ChunkSupporter

trait DefaultConsumer[ST <: Store[ST], H <: Heap[H],
											PC <: PathConditions[PC], S <: State[ST, H, S]]
		extends Consumer[DirectChunk, ST, H, S, DefaultContext]
		{ this: Logging with Evaluator[ST, H, S, DefaultContext]
									  with Brancher[ST, H, S, DefaultContext]
                    with ChunkSupporter[ST, H, PC, S] =>

  private type C = DefaultContext

	protected val decider: Decider[ST, H, PC, S, C]
	import decider.assume

	protected val stateFormatter: StateFormatter[ST, H, S, String]
	protected val bookkeeper: Bookkeeper
	protected val config: Config

  /*
   * ATTENTION: The DirectChunks passed to the continuation correspond to the
   * chunks as they existed when the consume took place. More specifically,
   * the amount of permissions that come with these chunks is NOT the amount
   * that has been consumed, but the amount that was found in the heap.
   */
	def consume(σ: S, p: Term, φ: ast.Expression, pve: PartialVerificationError, c: C)
             (Q: (S, Term, List[DirectChunk], C) => VerificationResult)
             : VerificationResult =

    consume(σ, σ.h, p, φ.whenExhaling, pve, c)((h1, t, dcs, c1) =>
      Q(σ \ h1, t, dcs, c1))

  def consumes(σ: S,
               p: Term,
               φs: Seq[ast.Expression],
               pvef: ast.Expression => PartialVerificationError,
               c: C)
              (Q: (S, Term, List[DirectChunk], C) => VerificationResult)
              : VerificationResult =

    consumes(σ, σ.h, p, φs map (_.whenExhaling), pvef, c)(Q)

  private def consumes(σ: S,
                       h: H,
                       p: Term,
                       φs: Seq[ast.Expression],
                       pvef: ast.Expression => PartialVerificationError,
                       c: C)
                       (Q: (S, Term, List[DirectChunk], C) => VerificationResult)
                       : VerificationResult =

    /* TODO: See the code comment about produce vs. produces in DefaultProducer.produces.
     *       The same applies to consume vs. consumes.
     */

    if (φs.isEmpty)
      Q(σ \ h, Unit, Nil, c)
    else {
      val φ = φs.head

      if (φ.tail.isEmpty)
        consume(σ, h, p, φ, pvef(φ), c)((h1, s1, dcs1, c1) =>
          Q(σ \ h1, s1, dcs1, c1))
      else
        consume(σ, h, p, φ, pvef(φ), c)((h1, s1, dcs1, c1) =>
          consumes(σ, h1, p, φs.tail, pvef, c1)((h2, s2, dcs2, c2) => {
            val c3 = c2.snapshotRecorder match {
              case Some(sr) =>
                val sr1 = c1.snapshotRecorder.get
                val sr2 = c2.snapshotRecorder.get
                val snap1 = if (s1 == Unit) Unit else sr1.currentSnap
                val snap2 = if (s2 == Unit) Unit else sr2.currentSnap
                c2.copy(snapshotRecorder = Some(sr.copy(currentSnap = Combine(snap1, snap2))))
              case _ => c2}

            Q(h2, Combine(s1, s2), dcs1 ::: dcs2, c3)
          }))
    }

  protected def consume(σ: S, h: H, p: Term, φ: ast.Expression, pve: PartialVerificationError, c: C)
                       (Q: (H, Term, List[DirectChunk], C) => VerificationResult)
                       : VerificationResult = {

    if (!φ.isInstanceOf[ast.And]) {
      logger.debug(s"\nCONSUME ${φ.pos}: $φ")
      logger.debug(stateFormatter.format(σ))
      logger.debug("h = " + stateFormatter.format(h))
    }

		val consumed = φ match {
      case ast.And(a1, a2) if !φ.isPure =>
				consume(σ, h, p, a1, pve, c)((h1, s1, dcs1, c1) =>
					consume(σ, h1, p, a2, pve, c1)((h2, s2, dcs2, c2) => {
            val c3 = c2.snapshotRecorder match {
              case Some(sr) =>
                val sr1 = c1.snapshotRecorder.get
                val sr2 = c2.snapshotRecorder.get
                val snap1 = if (s1 == Unit) Unit else sr1.currentSnap
                val snap2 = if (s2 == Unit) Unit else sr2.currentSnap
                c2.copy(snapshotRecorder = Some(sr.copy(currentSnap = Combine(snap1, snap2))))
              case _ => c2}

						Q(h2, Combine(s1, s2), dcs1 ::: dcs2, c3)}))

      case ast.Implies(e0, a0) if !φ.isPure =>
				eval(σ, e0, pve, c)((t0, c1) =>
					branch(σ, t0, c,
						(c2: C) => consume(σ, h, p, a0, pve, c2)(Q),
						(c2: C) => Q(h, Unit, Nil, c2)))

      case ast.Ite(e0, a1, a2) if !φ.isPure =>
        eval(σ, e0, pve, c)((t0, c1) =>
          branch(σ, t0, c,
            (c2: C) => consume(σ, h, p, a1, pve, c2)(Q),
            (c2: C) => consume(σ, h, p, a2, pve, c2)(Q)))

      case ast.AccessPredicate(locacc, perm) =>
        withChunkIdentifier(σ, locacc, true, pve, c)((id, c1) =>
          eval(σ, perm, pve, c1)((tPerm, c2) =>
            decider.assert(σ, perms.IsNonNegative(tPerm)){
              case true =>
                chunkSupporter.consume(σ, h, id, PermTimes(p, tPerm), pve, c2, locacc, Some(φ))(Q)
              case false =>
                Failure[ST, H, S](pve dueTo NegativePermission(perm))}))

      case _: ast.InhaleExhale =>
        Failure[ST, H, S](ast.Consistency.createUnexpectedInhaleExhaleExpressionError(φ))

			/* Any regular Expressions, i.e. boolean and arithmetic.
			 * IMPORTANT: The expression is evaluated in the initial heap (σ.h) and
			 * not in the partially consumed heap (h).
			 */
      case _ =>
        decider.tryOrFail[(H, Term, List[DirectChunk], C)](σ, c)((σ1, QS, QF) => {
          eval(σ1, φ, pve, c)((t, c) =>
            decider.assert(σ1, t) {
              case true =>
                assume(t)
                QS((h, Unit, Nil, c))
              case false =>
                QF(Failure[ST, H, S](pve dueTo AssertionFalse(φ)))
            })
        })(Q.tupled)
/* Consume pure expression w/o trying heuristics in case of failure */
/*
        eval(σ, φ, pve, c)((t, c) =>
          decider.assert(σ, t) {
            case true =>
              assume(t)
              Q(h, Unit, Nil, c)
            case false =>
              Failure[ST, H, S](pve dueTo AssertionFalse(φ))})
*/
		}

		consumed
	}
}
