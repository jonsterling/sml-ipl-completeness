structure IPL =
struct
  (* intuitionistic propositional logic *)
  datatype prop =
      TRUE
    | FALSE
    | IMP of prop * prop
    | AND of prop * prop
    | OR of prop * prop

  type 'a lazy = unit -> 'a

  (* canonical evidence *)
  datatype evd =
      AX
    | LAM of (evd -> evd lazy)
    | PAIR of evd lazy * evd lazy
    | INL of evd lazy
    | INR of evd lazy

  exception Stuck

  (* noncanonical evidence *)
  fun AP (LAM f, x) = f x
    | AP _ = raise Stuck

  fun DECIDE (INL x, l, _) = l x ()
    | DECIDE (INR x, _, r) = r x ()
    | DECIDE _ = raise Stuck

  fun SPREAD (PAIR (x, y), f) = f (x (), y ())
    | SPREAD _ = raise Stuck

  structure Ctx = StringListDict

  (* sequent *)
  datatype seq = !- of prop Ctx.dict * prop
  infix !-

  type hyp = string

  (* a sequent is valid if evidence for the premises can be transformed into
   * evidence for the conclusion *)
  type seq_evd = (hyp -> evd) -> evd

  (* sequent calculus proofs for IPL *)
  datatype proof =
      HYP of hyp
    | TRUE_INTRO
    | AND_INTRO of proof * proof
    | OR_INTRO_L of proof
    | OR_INTRO_R of proof
    | IMP_INTRO of hyp * proof
    | FALSE_ELIM of hyp
    | AND_ELIM of hyp * (hyp * hyp * proof)
    | OR_ELIM of hyp * (hyp * proof) * (hyp * proof)

  local
    val counter = ref 0
  in
    fun fresh () =
      let
        val i = !counter
      in
        counter := i + 1;
        "@" ^ Int.toString i
      end
  end

  fun completeness (H !- G) (F : seq_evd) : proof =
    (* first, let's probe F to see how much it needs *)
    let
      datatype probe = INTRO of evd | ELIM of hyp
      exception Probe of hyp
      val probed = INTRO (F (fn i => raise Probe i)) handle Probe i => ELIM i
      fun subst x i rho = F (fn j => if i = j then x rho else rho j)
    in
      case probed of
           INTRO AX => TRUE_INTRO
         | INTRO (PAIR (M, N)) =>
             let
               val (P, Q) = case G of AND (P, Q) => (P, Q) | _ => raise Match
               val p = completeness (H !- P) (fn _ => M ())
               val q = completeness (H !- Q) (fn _ => N ())
             in
               AND_INTRO (p, q)
             end
         | INTRO (INL M) =>
             let
               val (P, Q) = case G of OR (P, Q) => (P, Q) | _ => raise Match
               val p = completeness (H !- P) (fn _ => M ())
             in
               OR_INTRO_L p
             end
         | INTRO (INR M) =>
             let
               val (P, Q) = case G of OR (P, Q) => (P, Q) | _ => raise Match
               val q = completeness (H !- Q) (fn _ => M ())
             in
               OR_INTRO_R q
             end
         | INTRO (LAM M) =>
             let
               val (P, Q) = case G of IMP (P, Q) => (P, Q) | _ => raise Match
               val x = fresh ()
               val H' = Ctx.insert H x P
               val p = completeness (H' !- Q) (fn rho => M (rho x) ())
             in
               IMP_INTRO (x, p)
             end
         | ELIM i =>
             (case Ctx.lookup H i of
                  OR (P, Q) =>
                    let
                      val i1 = fresh ()
                      val i2 = fresh ()
                      val H1 = Ctx.insert H i1 P
                      val H2 = Ctx.insert H i2 Q
                    in
                      OR_ELIM
                        (i,
                         (i1, completeness (H1 !- G) (subst (fn rho => INL (fn _ => rho i1)) i)),
                         (i2, completeness (H2 !- G) (subst (fn rho => INR (fn _ => rho i2)) i)))
                    end
                | AND (P, Q) =>
                    let
                      val i1 = fresh ()
                      val i2 = fresh ()
                      val H' = Ctx.insert (Ctx.insert H i1 P) i2 Q
                    in
                      AND_ELIM (i, (i1, i2, completeness (H' !- G) (subst (fn rho => PAIR (fn _ => rho i1, fn _ => rho i2)) i)))
                    end
                | TRUE =>
                    completeness
                      (H !- G)
                      (subst (fn _ => AX) i)
                | FALSE => FALSE_ELIM i
                | _ => raise Fail "ELIM")
    end

  val H = Ctx.insert Ctx.empty "x" (AND (TRUE, AND (TRUE, TRUE)))
  val test =
    completeness
      (H !- IMP (AND (TRUE, FALSE), AND (TRUE, TRUE)))
      (fn rho =>
        LAM (fn x => fn () => SPREAD (x, (fn (y, z) => PAIR (fn _ => y, fn _ => y))))
      )

end
