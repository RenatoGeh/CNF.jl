module CNF

const Variable = Int
const Literal = Int
const Clause = Set{Literal}
const Inst = Union{Vector{Literal}, Set{Literal}}
const Formula = Vector{Clause}
const Scope = Union{Vector{Variable}, Set{Variable}}
export Variable, Literal, Clause, Inst, Formula, Scope

const ⊤ = Clause()
const ⊥ = Clause(0)
export ⊤, ⊥

"Conjunctive Normal Form"
mutable struct CNF
  "Clauses in CNF."
  clauses::Formula
  "CNF Scope (set of variables."
  scope::Scope
  "CNF constructor for a given Formula and Scope."
  CNF(α::Formula, S::Scope) = new(α, S)
  "CNF constructor for a given Formula."
  CNF(α::Formula)::CNF = new(α, get_vars(α))
  "CNF constructor for a given Vector{Vector{Literal}}."
  function CNF(α::Vector{Vector{Literal}})::CNF
    β = broadcast(Clause, α)
    return new(β, get_vars(β))
  end
  "CNF constructor for a single literal."
  CNF(x::Literal)::CNF = new(Formula([Clause(x)]), scope(x))
  "CNF constructor for a single clause."
  CNF(σ::Clause)::CNF = new(Formula([σ]), scope(abs.(σ)))
end
export CNF

"Trims CNF to get rid of ⊤'s and ⊥'s."
function trim!(ϕ::CNF)::CNF
  C = ϕ.clauses
  is_bot = false
  for c ∈ C
    if c == ⊥
      is_bot = true
      break
    end
  end
  if is_bot ϕ.clauses = Formula([⊥])
  else
    filter!(c -> c != ⊤, C)
    if !isempty(C) # Deal with tautologies between clauses.
      # Mapping of all one-literal clauses.
      M = Dict{Variable, Int}()
      how_many = 0
      for c ∈ C
        if length(c) == 1
          x = first(c); v = abs(x)
          M[v] = haskey(M, v) ? M[v] + x : x
          how_many += 1
        end
      end
      # Contains at least two one-literal clauses of same variable.
      if how_many > 1 && length(M) != how_many
        filter!(c -> length(c) != 1, C)
        for (v, r) ∈ M
          if r == 0 # Then this is a ⊥ tautology.
            ϕ.clauses = Formula([⊥])
            ϕ.scope = scope()
            return ϕ
          else # Then this is either a positive or negative literal tautology.
            push!(ϕ.clauses, Clause(r > 0 ? v : -v))
          end
        end
      end
    end
    if isempty(ϕ.clauses) ϕ.clauses = Formula([⊤]) end
  end
  ϕ.scope = get_vars(ϕ.clauses)
  return ϕ
end
export trim!

"Performs Shannon's Decomposition on the CNF given a set of variables to isolate."
function shannon!(ϕ::CNF, V::Scope)::Vector{Tuple{Inst, CNF}}
  Δ = Vector{Tuple{Inst, CNF}}()
  for x ∈ valuations(V)
    push!(Δ, (x, trim!(ϕ|x)))
  end
  return Δ
end
export shannon!

"Performs Shannon's Decomposition on the CNF given a set of variables to isolate."
function shannon(ϕ::CNF, V::Scope)::Vector{Tuple{Inst, CNF}}
  Δ = Vector{Tuple{Inst, CNF}}()
  for x ∈ valuations(V)
    push!(Δ, (x, ϕ|x))
  end
  return Δ
end
export shannon

"Performs Shannon's Decomposition on the CNF given a variable to isolate."
@inline shannon(ϕ::CNF, v::Variable)::Tuple{Literal, CNF, Literal, CNF} = (v, ϕ|[v], -v, ϕ|[-v])

"Performs Shannon's Decomposition on the CNF given a variable to isolate and trim resulting clauses."
@inline shannon!(ϕ::CNF, v::Variable)::Tuple{Literal, CNF, Literal, CNF} = (v, trim!(ϕ|[v]), -v, trim!(ϕ|[-v]))

@inline trim(ϕ::CNF)::CNF = trim!(CNF(copy(ϕ.clauses), get_vars(ϕ.clauses)))
export trim

"Restrict formula to given (incomplete) instantiation."
function Base.:|(ϕ::CNF, X::Inst)::CNF
  if ϕ == ⊤ return CNF(⊤) end
  if X isa Vector{Literal} X = inst(X) end
  M = Dict{Variable, Literal}()
  for x ∈ X
    M[abs(x)] = x
  end
  S = scope()
  C = ϕ.clauses
  α = Formula()
  for c ∈ C
    # Find clauses which are true given X and replace with ⊤.
    top = false
    for x ∈ c
      v = abs(x)
      if haskey(M, v) && M[v] == x
        top = true
        break
      end
    end
    if top
      push!(α, ⊤)
      continue
    end
    # If clause is not tautology, reduce clause.
    σ = Clause()
    for x ∈ c
      v = abs(x)
      if !haskey(M, v)
        union!(σ, x)
        union!(S, v)
      end
      # Invariant: if haskey(M, v), then M[v] != x because otherwise it would be a tautology.
    end
    # If clause is empty, it means no literal assignment was true in clause, therefore ⊥.
    push!(α, isempty(σ) ? ⊥ : σ)
  end
  return CNF(α, S)
end

"Evaluate CNF."
function (ϕ::CNF)(X::Inst)::Bool
  M = Dict{Variable, Literal}()
  for x ∈ X
    M[abs(x)] = x
  end
  C = ϕ.clauses
  for c ∈ C
    l = false
    for v ∈ c
      # Assumes abs(v) is indeed in M. If that is not the case, it is not an evaluation, but a
      # restriction on the formula.
      if v == M[abs(v)]
        l = true
        break
      end
    end
    if !l return false end
  end
  return true
end

"Get all variables from CNF clauses."
@inline get_vars(α::Formula)::Scope = setdiff!(scope(unique(abs.(union(α...)))), ⊥)
export get_vars

"Count variables and assign mapping and number of variables."
@inline count_vars(α::Formula)::Int = return length(get_vars(α))
export count_vars

"Creates a CNF from a conjunction of two literals."
@inline function (∨)(a::Literal, b::Literal)::CNF
  return CNF(Formula([Clause((a, b))]), scope(abs(a), abs(b)))
end
export ∨

"Creates a CNF from a disjunction of two literals."
@inline function (∧)(a::Literal, b::Literal)::CNF
  return CNF(Formula([Clause(a), Clause(b)]), scope(abs(a), abs(b)))
end
export ∧

"Appends a literal to CNF as a new disjunction clause."
@inline function (∧)(ϕ::CNF, x::Literal)::CNF
  push!(ϕ.clauses, Clause(x))
  union!(ϕ.scope, abs(x))
  return ϕ
end

@inline (∧)(x::Literal, ϕ::CNF) = ϕ ∧ x

"Appends a literal to CNF as part of the right-most clause of CNF."
@inline function (∨)(ϕ::CNF, x::Literal)::CNF
  union!(last(ϕ.clauses), x)
  union!(ϕ.scope, abs(x))
  return ϕ
end

"Appends a CNF ψ to another CNF ϕ, appending to the left CNF."
@inline function (∧)(ϕ::CNF, ψ::CNF)::CNF
  append!(ϕ.clauses, ψ.clauses)
  union!(ϕ.scope, ψ.scope)
  return ϕ
end

Base.:(==)(ϕ::CNF, ψ::CNF)::Bool = ϕ.scope == ψ.scope && length(ϕ.clauses) == length(ψ.clauses) && ϕ.clauses ⊆ ψ.clauses

Base.:(==)(ϕ::CNF, α::Vector{Vector{Literal}})::Bool = length(ϕ.clauses) == length(α) && ϕ.clauses ⊆ α
Base.:(==)(α::Vector{Vector{Literal}}, ϕ::CNF)::Bool = ϕ == α

Base.:(==)(ϕ::CNF, α::Formula)::Bool = length(ϕ.clauses) == length(α) && ϕ.clauses ⊆ α
Base.:(==)(α::Formula, ϕ::CNF)::Bool = ϕ == α

Base.:(==)(ϕ::CNF, α::Clause)::Bool = α == ⊥ ? ⊥ ∈ ϕ.clauses : (length(ϕ.clauses) == 1 && first(ϕ.clauses) == α)
Base.:(==)(α::Clause, ϕ::CNF)::Bool = ϕ == α

Base.:∈(α::Clause, ϕ::CNF)::Bool = α ∈ ϕ.clauses
Base.:∋(ϕ::CNF, α::Clause)::Bool = α ∈ ϕ

# Guarantee same hash for same clause CNFs (not necessarily for all equivalent CNFs).
@inline Base.hash(ϕ::CNF, h::UInt) = hash((Set{Clause}(ϕ.clauses), ϕ.scope), h)

"Negated literal."
(¬)(v::Literal)::Literal = -v
export ¬

"Outputs a string representation of CNF."
function Base.string(ϕ::CNF)::String
  s = ""
  C = ϕ.clauses
  m = length(C)
  for (i, c) ∈ enumerate(C)
    s *= "("
    if c == ⊥
      s *= "⊥"
      @goto clause_end
    elseif c == ⊤
      s *= "⊤"
      @goto clause_end
    end
    n = length(c)
    for (j, v) ∈ enumerate(c)
      if v > 0 s *= "$v"
      else s *= "¬$(-v)" end
      if j != n s *= " ∨ " end
    end
    @label clause_end
    s *= ")"
    if i != m s *= " ∧ " end
  end
  return s
end

@inline firstlit(ϕ::CNF)::Literal = first(first(ϕ.clauses))
@inline firstclause(ϕ::CNF)::Clause = first(ϕ.clauses)
export firstlit, firstclause

Base.show(io::Core.IO, ϕ::CNF) = show(io, string(ϕ))
Base.print(io::Core.IO, ϕ::CNF) = print(io, string(ϕ))

@inline Base.copy(ϕ::CNF)::CNF = CNF(copy(ϕ.clauses), copy(ϕ.scope))
@inline function Base.copy!(ψ::CNF, ϕ::CNF)::CNF
  copy!(ψ.clauses, ϕ.clauses)
  copy!(ψ.scope, ϕ.clauses)
  return ψ
end

struct Permutations
  V::Scope
  m::Int
end

"Get the set of all instantiations of the given variables. Returns an iterator."
@inline valuations(V::Scope) = Permutations(V, 2^length(V))
export valuations

function Base.iterate(P::Permutations, state=0)::Union{Nothing, Tuple{Inst, Integer}}
  s = state + 1
  if state == 0 return inst(broadcast(¬, P.V)), s end
  if state >= P.m return nothing end
  V, n = collect(P.V), length(P.V)
  return inst((i -> (state >> (i-1)) & 1 == 1 ? V[i] : -V[i]).(1:n)), s
end

@inline Base.:(==)(X::Inst, Y::Vector{Literal}) = X == Set(Y)
@inline Base.:(==)(Y::Vector{Literal}, X::Inst) = X == Set(Y)

@inline inst_str(X::Inst; del::String=" ") = join((x -> x > 0 ? " $x" : "¬$(-x)").(X), del)
export inst_str

@inline lit_str(x::Literal) = x > 0 ? Base.string(x) : x < 0 ? "¬$(-x)" : "⊥"
export lit_str

@inline inst(X::Vector{Literal}) = Set{Literal}(X)
@inline inst(X::Vararg{Literal}) = Set{Literal}(X)
@inline scope(X::Vector{Variable}) = Set{Variable}(X)
@inline scope(X::Vararg{Variable}) = Set{Variable}(X)
@inline scope(X::Vector{UInt32}) = Set{Variable}(convert(Vector{Variable}, X))
@inline scope(X::Vararg{UInt32}) = Set{Variable}(convert.(Int, X))
@inline scope(X::UnitRange{Int}) = Set{Variable}(X)
@inline scope() = Set{Variable}()
export inst, scope

@inline and(X::Inst) = CNF(Formula(Clause.(X)))
@inline or(X::Inst) = CNF(Set{Literal}(X))
export and, or

@inline is_⊤(ϕ::CNF) = length(ϕ.clauses) == 1 && first(ϕ.clauses) == ⊤
@inline is_⊥(ϕ::CNF) = ⊥ ∈ ϕ.clauses
export is_⊤, is_⊥

"Remove dupplicate literals."
@inline function rmdups!(Φ::Vector{Inst})
  dups = intersect(Φ...)
  if !isempty(dups) foreach(ϕ -> setdiff!(ϕ, dups), Φ) end
end
@inline rmdups(Φ::Vector{Inst}) = rmdups!(copy(Φ))
export rmdups, rmdups!

end # module
