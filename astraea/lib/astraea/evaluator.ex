defmodule Astraea.Evaluator do
  @moduledoc """
  Sandboxed Term Reducer, Model-Probe, and Example-Guided Evaluator on the BEAM.

  Provides:
    * `eval/4` - Normalizes typed lambda-calculus terms and combinator applications
      to normal form via beta-reduction, combinator reduction (S, K, I, B, C),
      equality evaluation, boolean connectives, and arithmetic simplification.
    * `eval_sandboxed/4` - Evaluates terms inside an isolated BEAM process under an
      execution budget and wall-clock timeout (`Task.yield` / process monitor),
      ensuring termination safety for untrusted or complex higher-order terms.
    * `eval_clause/4` - Evaluates ground literals in a clause, dropping false literals.
    * `simplify_clause/4` - Evaluates a clause and returns `:unchanged`, `:tautology`,
      or `{:simplified, new_clause}`.
    * `find_counterexample/4` - Evaluates candidate assignments over finite domains / booleans
      to refute conjectures or clauses early (QuickCheck/Nitpick style).
    * `filter_candidate_lambda/4` - Tests candidate lambda abstractions against concrete
      input-output example pairs to prune unsound Primitive Substitution (`PrimSubst`) branches.
  """

  alias Astraea.{Arena, ProofChecker}
  alias Astraea.Calculus.Terms
  alias Astraea.Input.Arith

  @tag_const 1
  @tag_bvar 2
  @tag_fvar 3
  @tag_app 4
  @tag_lam 5
  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9
  @tag_comb 11

  @comb_s 1
  @comb_k 2
  @comb_i 3
  @comb_b 4
  @comb_c 5

  @ty_o 0

  @default_max_steps 10_000

  @type env :: %{non_neg_integer() => Arena.term_id()}

  # ---------------------------------------------------------------------------
  # Core Evaluation / Reduction
  # ---------------------------------------------------------------------------

  @doc """
  Evaluates `term_id` in `arena` under substitution/environment `env` to normal form.

  Supports:
    - Beta-reduction of lambda abstractions: `(^ [X]: body) @ arg -> body[0 |-> arg]`
    - Combinator reductions: `I x -> x`, `K a x -> a`, `B f g x -> f (g x)`,
      `C f g x -> f x g`, `S f g x -> (f x) (g x)`
    - Boolean connectives: `~`, `|`, `&`, `=>`, `<=>`
    - Equality: syntactic identity `t = t -> $true`, boolean inequality `$true = $false -> $false`,
      arithmetic equality, and optional distinct constants
    - Universal quantifiers over booleans (`$o`)
    - Environment substitutions for free variables
  """
  @spec eval(Arena.t(), Arena.term_id(), env(), keyword()) :: {Arena.t(), Arena.term_id()}
  def eval(%Arena{} = arena, term_id, env \\ %{}, opts \\ []) do
    max_steps = Keyword.get(opts, :max_steps, @default_max_steps)
    {arena, norm_id, _steps} = do_eval(arena, term_id, env, opts, max_steps)
    {arena, norm_id}
  end

  defp do_eval(%Arena{} = arena, term_id, _env, _opts, steps) when steps <= 0 do
    {arena, term_id, 0}
  end

  defp do_eval(%Arena{} = arena, term_id, env, opts, steps) do
    {tag, _flags, _ty_id, left, right} = Arena.get_node(arena, term_id)

    case tag do
      @tag_const ->
        {arena, term_id, steps}

      @tag_bvar ->
        {arena, term_id, steps}

      @tag_fvar ->
        case Map.fetch(env, left) do
          {:ok, rep_id} ->
            do_eval(arena, rep_id, env, opts, steps - 1)

          :error ->
            {arena, term_id, steps}
        end

      @tag_comb ->
        {arena, term_id, steps}

      @tag_lam ->
        if Keyword.get(opts, :full_norm, false) do
          {arena, body_norm, steps} = do_eval(arena, right, env, opts, steps - 1)
          {arena, lam_id} = Arena.mk_lam(arena, left, body_norm)
          {arena, lam_id, steps}
        else
          {arena, term_id, steps}
        end

      @tag_app ->
        eval_app(arena, left, right, env, opts, steps)

      @tag_not ->
        {arena, inner, steps} = do_eval(arena, left, env, opts, steps - 1)

        cond do
          is_true?(arena, inner) ->
            {arena, false_id} = truth(arena, false)
            {arena, false_id, steps}

          is_false?(arena, inner) ->
            {arena, true_id} = truth(arena, true)
            {arena, true_id, steps}

          elem(Arena.get_node(arena, inner), 0) == @tag_not ->
            {@tag_not, _, _, inner_inner, _} = Arena.get_node(arena, inner)
            do_eval(arena, inner_inner, env, opts, steps - 1)

          true ->
            {arena, not_id} = Arena.mk_not(arena, inner)
            {arena, not_id, steps}
        end

      @tag_or ->
        {arena, l_val, steps} = do_eval(arena, left, env, opts, steps - 1)

        if is_true?(arena, l_val) do
          {arena, true_id} = truth(arena, true)
          {arena, true_id, steps}
        else
          {arena, r_val, steps} = do_eval(arena, right, env, opts, steps - 1)

          cond do
            is_true?(arena, r_val) ->
              {arena, true_id} = truth(arena, true)
              {arena, true_id, steps}

            is_false?(arena, l_val) ->
              {arena, r_val, steps}

            is_false?(arena, r_val) ->
              {arena, l_val, steps}

            l_val == r_val ->
              {arena, l_val, steps}

            true ->
              {arena, or_id} = Arena.mk_or(arena, l_val, r_val)
              {arena, or_id, steps}
          end
        end

      @tag_eq ->
        {arena, l_val, steps} = do_eval(arena, left, env, opts, steps - 1)
        {arena, r_val, steps} = do_eval(arena, right, env, opts, steps - 1)

        cond do
          l_val == r_val ->
            {arena, true_id} = truth(arena, true)
            {arena, true_id, steps}

          (is_true?(arena, l_val) and is_false?(arena, r_val)) or
              (is_false?(arena, l_val) and is_true?(arena, r_val)) ->
            {arena, false_id} = truth(arena, false)
            {arena, false_id, steps}

          distinct_constants?(arena, l_val, r_val, opts) ->
            {arena, false_id} = truth(arena, false)
            {arena, false_id, steps}

          true ->
            {arena, eq_id} = Arena.mk_eq(arena, l_val, r_val)

            # Check arithmetic evaluation if available
            if Keyword.get(opts, :eval_arith, true) and arithmetic?(arena) do
              {arena, arith_id} = Arith.eval(arena, eq_id)
              {arena, arith_id, steps}
            else
              {arena, eq_id, steps}
            end
        end

      @tag_forall ->
        eval_forall(arena, left, right, env, opts, steps)

      _ ->
        {arena, term_id, steps}
    end
  end

  defp eval_app(%Arena{} = arena, fun_id, arg_id, env, opts, steps) do
    {arena, f_val, steps} = do_eval(arena, fun_id, env, opts, steps - 1)

    case Arena.get_node(arena, f_val) do
      # Beta-reduction: (^ [X]: body) @ arg -> body[0 |-> arg]
      {@tag_lam, _, _, _dom, body} ->
        {arena, arg_val, steps} = do_eval(arena, arg_id, env, opts, steps - 1)
        {arena, subbed} = Arena.subst_bvar(arena, body, 0, arg_val)
        do_eval(arena, subbed, env, opts, steps - 1)

      # Combinator I: I x -> x
      {@tag_comb, _, _, @comb_i, _} ->
        do_eval(arena, arg_id, env, opts, steps - 1)

      # Combinator K application: (K a) x -> a
      {@tag_app, _, _, k_head, a_arg} ->
        case Arena.get_node(arena, k_head) do
          {@tag_comb, _, _, @comb_k, _} ->
            do_eval(arena, a_arg, env, opts, steps - 1)

          # Ternary combinators B, C, S
          {@tag_app, _, _, comb_head, first_arg} ->
            eval_ternary_comb(arena, comb_head, first_arg, a_arg, arg_id, env, opts, steps)

          _ ->
            finish_app(arena, f_val, arg_id, env, opts, steps)
        end

      _ ->
        finish_app(arena, f_val, arg_id, env, opts, steps)
    end
  end

  defp eval_ternary_comb(%Arena{} = arena, comb_head, f_arg, g_arg, x_arg, env, opts, steps) do
    case Arena.get_node(arena, comb_head) do
      # B f g x -> f @ (g @ x)
      {@tag_comb, _, _, @comb_b, _} ->
        {arena, gx} = Arena.mk_app(arena, g_arg, x_arg)
        {arena, fgx} = Arena.mk_app(arena, f_arg, gx)
        do_eval(arena, fgx, env, opts, steps - 1)

      # C f g x -> f @ x @ g
      {@tag_comb, _, _, @comb_c, _} ->
        {arena, fx} = Arena.mk_app(arena, f_arg, x_arg)
        {arena, fxg} = Arena.mk_app(arena, fx, g_arg)
        do_eval(arena, fxg, env, opts, steps - 1)

      # S f g x -> (f @ x) @ (g @ x)
      {@tag_comb, _, _, @comb_s, _} ->
        {arena, fx} = Arena.mk_app(arena, f_arg, x_arg)
        {arena, gx} = Arena.mk_app(arena, g_arg, x_arg)
        {arena, fgx} = Arena.mk_app(arena, fx, gx)
        do_eval(arena, fgx, env, opts, steps - 1)

      _ ->
        finish_app(
          arena,
          elem(
            Arena.mk_app(arena, elem(Arena.mk_app(arena, comb_head, f_arg), 1), g_arg),
            1
          ),
          x_arg,
          env,
          opts,
          steps
        )
    end
  end

  defp finish_app(%Arena{} = arena, f_val, arg_id, env, opts, steps) do
    {arena, arg_val, steps} = do_eval(arena, arg_id, env, opts, steps - 1)
    {arena, app_id} = Arena.mk_app(arena, f_val, arg_val)

    if Keyword.get(opts, :eval_arith, true) and arithmetic?(arena) do
      {arena, arith_id} = Arith.eval(arena, app_id)
      {arena, arith_id, steps}
    else
      {arena, app_id, steps}
    end
  end

  defp eval_forall(%Arena{} = arena, dom_id, body_id, env, opts, steps) do
    # Quantification over booleans: ! [X: $o]: body(X) <=> body($true) & body($false)
    if dom_id == @ty_o and Keyword.get(opts, :unroll_bool_forall, true) do
      {arena, true_const} = truth(arena, true)
      {arena, false_const} = truth(arena, false)

      {arena, t_sub} = Arena.subst_bvar(arena, body_id, 0, true_const)
      {arena, f_sub} = Arena.subst_bvar(arena, body_id, 0, false_const)

      {arena, t_eval, steps} = do_eval(arena, t_sub, env, opts, steps - 1)

      if is_false?(arena, t_eval) do
        {arena, false_id} = truth(arena, false)
        {arena, false_id, steps}
      else
        {arena, f_eval, steps} = do_eval(arena, f_sub, env, opts, steps - 1)

        cond do
          is_false?(arena, f_eval) ->
            {arena, false_id} = truth(arena, false)
            {arena, false_id, steps}

          is_true?(arena, t_eval) and is_true?(arena, f_eval) ->
            {arena, true_id} = truth(arena, true)
            {arena, true_id, steps}

          true ->
            {arena, conj} = Arena.mk_and(arena, t_eval, f_eval)
            {arena, conj, steps}
        end
      end
    else
      {arena, forall_id} = Arena.mk_forall(arena, dom_id, body_id)
      {arena, forall_id, steps}
    end
  end

  # ---------------------------------------------------------------------------
  # Sandboxed Execution on the BEAM
  # ---------------------------------------------------------------------------

  @doc """
  Runs `eval/4` inside an isolated BEAM process with a timeout and reduction budget.
  Guarantees that infinite loops or non-terminating terms never block or crash
  the caller process.
  """
  @spec eval_sandboxed(Arena.t(), Arena.term_id(), env(), non_neg_integer()) ::
          {:ok, Arena.t(), Arena.term_id()}
          | {:timeout, Arena.t(), Arena.term_id()}
          | {:error, term()}
  def eval_sandboxed(%Arena{} = arena, term_id, env \\ %{}, timeout_ms \\ 100) do
    parent = self()
    ref = make_ref()

    {pid, mon} =
      spawn_monitor(fn ->
        try do
          result = eval(arena, term_id, env, max_steps: 50_000)
          send(parent, {ref, :ok, result})
        rescue
          e -> send(parent, {ref, :error, e})
        catch
          :exit, r -> send(parent, {ref, :exit, r})
        end
      end)

    receive do
      {^ref, :ok, {ar, res_id}} ->
        Process.demonitor(mon, [:flush])
        {:ok, ar, res_id}

      {^ref, :error, reason} ->
        Process.demonitor(mon, [:flush])
        {:error, reason}

      {^ref, :exit, reason} ->
        Process.demonitor(mon, [:flush])
        {:error, reason}

      {:DOWN, ^mon, :process, ^pid, reason} ->
        {:error, {:process_down, reason}}
    after
      timeout_ms ->
        Process.demonitor(mon, [:flush])
        Process.exit(pid, :kill)
        {:timeout, arena, term_id}
    end
  end

  # ---------------------------------------------------------------------------
  # Clausal Evaluation & Simplification (LCF Kernel Justification)
  # ---------------------------------------------------------------------------

  @doc """
  Evaluates all ground literals in `clause`, dropping false literals (`{:pos, $false}`,
  `{:neg, $true}`).
  """
  @spec eval_clause(Arena.t(), ProofChecker.clause(), env(), keyword()) ::
          {Arena.t(), ProofChecker.clause()}
  def eval_clause(%Arena{} = arena, clause, env \\ %{}, opts \\ []) do
    {arena, true_id} = truth(arena, true)
    {arena, false_id} = truth(arena, false)

    Enum.reduce(clause, {arena, MapSet.new()}, fn {pol, atom}, {ar, acc} ->
      {ar, atom2} = eval(ar, atom, env, opts)

      case {pol, atom2} do
        {:pos, ^false_id} -> {ar, acc}
        {:neg, ^true_id} -> {ar, acc}
        lit -> {ar, MapSet.put(acc, lit)}
      end
    end)
  end

  @doc """
  Prover-facing clausal simplification: evaluates ground literals and returns
  `{arena, :unchanged}`, `{arena, :tautology}` (if a literal evaluated to true),
  or `{arena, {:simplified, new_clause}}`.
  """
  @spec simplify_clause(Arena.t(), ProofChecker.clause(), env(), keyword()) ::
          {Arena.t(), :unchanged | :tautology | {:simplified, ProofChecker.clause()}}
  def simplify_clause(%Arena{} = arena, clause, env \\ %{}, opts \\ []) do
    {arena, result} = eval_clause(arena, clause, env, opts)
    {arena, true_id} = truth(arena, true)
    {arena, false_id} = truth(arena, false)

    cond do
      result == clause ->
        {arena, :unchanged}

      MapSet.member?(result, {:pos, true_id}) or MapSet.member?(result, {:neg, false_id}) ->
        {arena, :tautology}

      true ->
        {arena, {:simplified, result}}
    end
  end

  # ---------------------------------------------------------------------------
  # Proof by Example: Counterexample / Finite Model Finding
  # ---------------------------------------------------------------------------

  @doc """
  Attempts to find a finite model / boolean assignment that satisfies `axioms`
  while refuting `conj_term_id` (evaluating to `$false`).

  Returns `{:counterexample, env}` or `:not_found`.
  """
  @spec find_counterexample(Arena.t(), Arena.term_id(), [Arena.term_id()], keyword()) ::
          {:counterexample, env()} | :not_found
  def find_counterexample(%Arena{} = arena, conj_term_id, axioms \\ [], opts \\ []) do
    # Collect boolean free variables across conjecture and axioms
    conj_fvars = Arena.free_vars(arena, conj_term_id)

    all_fvars =
      Enum.reduce(axioms, conj_fvars, fn ax_id, acc ->
        MapSet.union(acc, Arena.free_vars(arena, ax_id))
      end)

    bool_fvars =
      all_fvars
      |> Enum.filter(fn {_var_id, ty_id} -> ty_id == @ty_o end)
      |> Enum.map(&elem(&1, 0))

    max_vars = Keyword.get(opts, :max_bool_vars, 8)

    if bool_fvars != [] and length(bool_fvars) <= max_vars do
      {arena, true_id} = truth(arena, true)
      {arena, false_id} = truth(arena, false)
      values = [true_id, false_id]

      assignments = enumerate_assignments(bool_fvars, values)

      Enum.find_value(assignments, :not_found, fn env ->
        # Check if all axioms hold under this assignment
        axioms_hold? =
          Enum.all?(axioms, fn ax_id ->
            {_ar, ax_val} = eval(arena, ax_id, env, opts)
            not is_false?(arena, ax_val)
          end)

        if axioms_hold? do
          {_ar, conj_val} = eval(arena, conj_term_id, env, opts)

          if is_false?(arena, conj_val) do
            {:counterexample, env}
          else
            nil
          end
        else
          nil
        end
      end)
    else
      :not_found
    end
  end

  defp enumerate_assignments([], _values), do: [%{}]

  defp enumerate_assignments([var | rest], values) do
    rest_assigns = enumerate_assignments(rest, values)

    for val <- values, assign <- rest_assigns do
      Map.put(assign, var, val)
    end
  end

  # ---------------------------------------------------------------------------
  # Proof by Example: Candidate Lambda Filter (for PrimSubst / Choice)
  # ---------------------------------------------------------------------------

  @doc """
  Tests a candidate lambda-abstraction `cand_lam_id` against a list of
  input-output example pairs `[{input_term_id, expected_out_id}]`.

  Returns `true` if all examples pass (`(cand_lam_id @ input) == expected`),
  or `false` if any example is refuted by evaluation.
  """
  @spec filter_candidate_lambda(
          Arena.t(),
          Arena.term_id(),
          [{Arena.term_id(), Arena.term_id()}],
          keyword()
        ) :: boolean()
  def filter_candidate_lambda(%Arena{} = arena, cand_lam_id, examples, opts \\ []) do
    Enum.all?(examples, fn {input_id, expected_out_id} ->
      {ar, app_id} = Arena.mk_app(arena, cand_lam_id, input_id)
      {_ar, evaluated_id} = eval(ar, app_id, %{}, opts)
      evaluated_id == expected_out_id
    end)
  end

  # ---------------------------------------------------------------------------
  # Helpers
  # ---------------------------------------------------------------------------

  @doc "Returns true iff `term_id` is `$true`."
  @spec is_true?(Arena.t(), Arena.term_id()) :: boolean()
  def is_true?(%Arena{} = arena, term_id) do
    Terms.const_named?(arena, term_id, "$true")
  end

  @doc "Returns true iff `term_id` is `$false`."
  @spec is_false?(Arena.t(), Arena.term_id()) :: boolean()
  def is_false?(%Arena{} = arena, term_id) do
    Terms.const_named?(arena, term_id, "$false")
  end

  defp truth(%Arena{} = arena, true), do: Arena.mk_const(arena, "$true", :o)
  defp truth(%Arena{} = arena, false), do: Arena.mk_const(arena, "$false", :o)

  defp arithmetic?(%Arena{} = arena) do
    Enum.any?(["$int", "$rat", "$real"], &Map.has_key?(arena.types, {:base, &1}))
  end

  defp distinct_constants?(%Arena{} = arena, l_val, r_val, opts) do
    if Keyword.get(opts, :distinct_constants, false) do
      node_l = Arena.get_node(arena, l_val)
      node_r = Arena.get_node(arena, r_val)

      case {node_l, node_r} do
        {{@tag_const, _, ty_l, sym_l, _}, {@tag_const, _, ty_r, sym_r, _}} ->
          ty_l == ty_r and sym_l != sym_r

        _ ->
          false
      end
    else
      false
    end
  end
end
