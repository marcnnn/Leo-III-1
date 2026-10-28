defmodule Astraea.Calculus.Fluid do
  @moduledoc """
  Fluid superposition (FluidSup of λSup; Bentkamp, Blanchette, Tourret, Vukmirović
  and Waldmann, "Superposition for Higher-Order Logic", JAR 2023), Pillar 3 of
  `Notes/beating_zipperposition_plan.md`.

  A subterm is *fluid* if instantiation can make a redex appear inside it. Plain
  superposition only rewrites at positions unifiable with `l`; at a fluid
  `Y u1 ... um` (`Y` free, `m >= 1`) FluidSup instead solves `Y us =? Z l` for a
  fresh `Z` and rewrites `Z l` to `Z r`. Pre-unification (`Calculus.Unify`) closes
  that flex-flex pair with bindings that drop `l`, so the inference would never
  fire. This module builds the most general solution that keeps `l` directly:

      Y := ^ [x1 ... xm]: G @ x1 ... @ xm @ l       (G fresh)

  Under it `Y us` becomes `G us l`, which contains `l`, and the prover's ordinary
  paramodulation turns it into `G us r`. That is FluidSup with `Z := ^ [y]: G us y`.

  Fluid lambdas (`^ [x]: s` with a free variable in `s`) are not handled.

  The binding is a substitution instance, so the step is a kernel `:subst` on the
  target clause followed by the existing `:paramod`; the kernel is unchanged.
  """

  alias Astraea.Arena
  alias Astraea.Calculus.Terms

  @doc "Whether `term` is an applied free variable `Y u1 ... um` with `m >= 1`."
  @spec fluid?(Arena.t(), Arena.term_id()) :: boolean()
  def fluid?(%Arena{} = arena, term) do
    {head, args} = Terms.spine(arena, term)
    args != [] and Terms.fvar?(arena, head)
  end

  @doc """
  The FluidSup binding for rewriting `from` inside the fluid subterm `target`:
  `{:ok, arena, next_fvar, subst}`, or `:error` if `target` is not fluid or its
  head occurs in `from`.
  """
  @spec binding(Arena.t(), non_neg_integer(), Arena.term_id(), Arena.term_id()) ::
          {:ok, Arena.t(), non_neg_integer(), Arena.subst()} | :error
  def binding(%Arena{} = arena, next_fvar, target, from) do
    {head, args} = Terms.spine(arena, target)

    with true <- args != [] and Terms.fvar?(arena, head),
         {_, _, _, y, _} = Arena.get_node(arena, head),
         false <- Enum.any?(Arena.free_vars(arena, from), &(elem(&1, 0) == y)),
         false <- Arena.has_loose_bvar?(arena, from, 0) do
      taus = Enum.map(args, &Arena.type_of(arena, &1))

      {arena, g_ty} =
        Terms.mk_arrows(arena, taus ++ [Arena.type_of(arena, from)], Arena.type_of(arena, target))

      {arena, g} = Arena.mk_fvar(arena, next_fvar, g_ty)
      {arena, xs} = Terms.bound_args(arena, taus)
      {arena, body} = Terms.mk_apps(arena, g, xs ++ [from])
      {arena, lam} = Terms.mk_lams(arena, taus, body)
      {:ok, arena, next_fvar + 1, %{y => lam}}
    else
      _ -> :error
    end
  end
end
