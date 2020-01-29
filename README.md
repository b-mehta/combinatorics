# Combinatorics in lean

<!-- vscode-markdown-toc -->
* [What is this?](#Whatisthis)
* [How can I install this package?](#HowcanIinstallthispackage)
* [Why did you choose this bit of maths to formalise?](#Whydidyouchoosethisbitofmathstoformalise)
* [What's the Kruskal-Katona theorem?](#WhatstheKruskal-Katonatheorem)
	* [What form do you prove it in?](#Whatformdoyouproveitin)
* [Can I contribute?](#CanIcontribute)
* [Where did you get the proofs from?](#Wheredidyougettheproofsfrom)
* [What's in this package?](#Whatsinthispackage)
	* [to_mathlib.lean](#to_mathlib.lean)
	* [basic.lean](#basic.lean)
	* [shadows.lean](#shadows.lean)
	* [colex.lean](#colex.lean)
	* [compressions/*.lean](#compressions.lean)
	* [kruskal_katona.lean](#kruskal_katona.lean)
* [Doesn't some of this belong in mathlib?](#Doesntsomeofthisbelonginmathlib)

<!-- vscode-markdown-toc-config
	numbering=false
	autoSave=true
	/vscode-markdown-toc-config -->
<!-- /vscode-markdown-toc -->

## <a name='Whatisthis'></a>What is this?

A [Lean](https://leanprover.github.io/) package formalising some combinatorics of finite sets, in particular the [Kruskal-Katona theorem](https://en.wikipedia.org/wiki/Kruskal-Katona_theorem) and some related results.

## <a name='HowcanIinstallthispackage'></a>How can I install this package?
First install Lean and mathlib using the [instructions here](https://github.com/leanprover-community/mathlib), and then
```
git clone https://github.com/b-mehta/combinatorics.git
cd combinatorics
leanpkg configure
update-mathlib
```

## <a name='Whydidyouchoosethisbitofmathstoformalise'></a>Why did you choose this bit of maths to formalise?

Combinatorics tends to have problems which are easy to state but hard to prove. In particular, the difficulty is usually in the proofs rather than in complicated definitions, so I thought to get to grips with Lean it'd be a good idea to formalise some of these proofs.
The main goal was to formalise the Kruskal-Katona theorem, but along the way I also formalised the local LYM inequality and LYM inequality, Sperner's theorem and a consequence of the Kruskal-Katona theorem called the Erdős-Ko-Rado theorem.

## <a name='WhatstheKruskal-Katonatheorem'></a>What's the Kruskal-Katona theorem?

In brief, the Kruskal-Katona theorem tells us the minimum possible size of the shadow of certain set families.
Picking apart what this means, a set family is just a collection (set) of subsets of a fixed finite 'universe' of elements - typically write `[n] := {0,...,n-1}`. 
Kruskal-Katona is concerned particular with set families in which every element has the same size, for instance 
```
A = { {0,1,2}, {0,1,3}, {0,2,3}, {0,2,4} }.
```
Each set in here would be called a 3-set, since each set has three elements.

The shadow of such a set family is everything we can get by removing an element from each set, and it's written `∂`. In our example,
```
∂A = { {0,1}, {0,2}, {0,3}, {0,4}, {1,2}, {1,3}, {2,3}, {2,4} }.
```
A question we could ask about shadows is

> If `A` is a set of `r`-sets, and the number of sets in `A` is fixed, how small can we make the shadow of `A`?

Ultimately, this is asking "How tightly can we pack some `r`-sets?". 
In particular, we'll say that we've fixed `r` and fixed `n`, so we can only take elements from `[n] = {0,...,n-1}`.

If we fix the size of `A` to be `C(k, r)` (the binomial coefficient) for some `k`, it seems reasonable that the best `A` would be all `r`-sets taking elements from `[k]`.

Kruskal-Katona says that this is the minimum, in particular if `|A| = C(k, r)`, then `|∂A| ≥ C(k, r-1)`. Actually, Kruskal-Katona gives a stronger result: for any value of `|A|` it gives the minimum value of `|∂A|` (although in this package, we don't prove it in this exact form).

### <a name='Whatformdoyouproveitin'></a>What form do you prove it in?
To write the Kruskal-Katona theorem in more general form in which it's formalised here, let's first define an ordering on `r`-sets called the colexicographic ordering, or colex for short. The colex ordering effectively tries to avoid large numbers. For `r = 2`, it starts like this:
```
{0,1}, {0,2}, {1,2}, {0,3}, {1,3}, {2,3}, {0,4}, {1,4}, {2,4}, {3,4}, ...
```
Notice how it reached `{2,3}` before `{1,4}`, because it tried to avoid getting `4`.
Also, observe that the first three sets above gives all `2`-sets from `[3]`, the first six sets give all `2`-sets from `[4]`, and so on, which were our guess for the minimum shadow families.

The Kruskal-Katona theorem then says
> If `A` is a family of `r`-sets, and `C` is the first `|A|` `r`-sets in colex, then `|∂A| ≥ |∂C|`.

## <a name='CanIcontribute'></a>Can I contribute? 
Yes! Take a look at the issues tab of the repository, there's a couple of things that could be added. Pull requests are very welcome.

## <a name='Wheredidyougettheproofsfrom'></a>Where did you get the proofs from?
The proofs are adapted from [my notes](https://www.b-mehta.co.uk/iii/mich/combinatorics.pdf) of Imre Leader's Cambridge Part III Combinatorics course in 2018.

## <a name='Whatsinthispackage'></a>What's in this package?
### <a name='to_mathlib.lean'></a>to_mathlib.lean
A fair few lemmas came up along the way, and some of them seemed like they ought to have already been in mathlib, so I've collected them in `to_mathlib.lean`. In my opinion they belong in mathlib, but I haven't yet got round to making the PRs myself. Feel free to do this if you'd like to help.

### <a name='basic.lean'></a>basic.lean
We first set up some basic definitions and lemmas for general combinatorics in `basic.lean` such as the definition of an antichain.
An antichain is a set family in which no set is contained in another, for instance
```
{ {0}, {4,6,7}, {2,4,5,6} }
```
### <a name='shadows.lean'></a>shadows.lean
In `shadows.lean`, we define the basic notion of a shadow. An important theorem relating to shadows is the local LYM theorem, which is then used to prove the LYM (Lubell-Yamamoto-Meshalkin) inequality:

> If `A` is an antichain, then 
>
> ![equation](https://latex.codecogs.com/svg.latex?%5Csum_%7Br%3D0%7D%5En%20%5Cfrac%7B%7C%5C%7BB%20%5Cin%20%5Cmathcal%7BA%7D%20%3A%20%7CB%7C%20%3D%20r%5C%7D%7C%7D%7B%5Cbinom%7Bn%7D%7Br%7D%7D%20%5Cleq%201)

Finally, this inequality is used to prove Sperner's theorem:

> If `A` is an antichain, then 
>
> ![equation](https://latex.codecogs.com/svg.latex?%7C%5Cmathcal%7BA%7D%7C%20%5Cleq%20%5Cbinom%7Bn%7D%7B%5Clfloor%5Cfrac%7Bn%7D%7B2%7D%5Crfloor%7D)

### <a name='colex.lean'></a>colex.lean
Defines the colex ordering and proves a couple of properties and lemmas relating to it.

### <a name='compressions.lean'></a>compressions/*.lean
To prove the Kruskal-Katona theorem, it is useful to use compressions (sometimes called shifting operators). 
The idea of a compression to "squash" a set family into something which might have a smaller shadow, but the same size. An `i,j`-compression does reduce the shadow of a set family, so an idea might be to keep applying them until we can't any more, and hope this gives the minimum shadow. Unfortunately this doesn't exactly work, but `i,j`-compressions are defined anyway in `compressions/ij.lean`, along with a proof that they do decrease the shadow.

One (not the only) approach to fixing this argument is to use more general `U,V`-compressions, defined in `compressions/UV.lean`. They can be a bit more drastic, and it turns out that if a set family is fully `U,V`-compressed, it is an initial segment of colex. The drawback to this approach is that `U,V`-compressions only decrease the shadow under certain conditions. So, the general idea of the proof is to apply these `U,V`-compressions in just the right order, until we can't apply any. Then the resultant family has a smaller shadow, and it's an initial segment of colex, which is what we wanted. 

### <a name='kruskal_katona.lean'></a>kruskal_katona.lean
In `kruskal_katona.lean` we prove the Kruskal-Katona theorem! 
Here's the statement (`X` is notation for `fin n`, i.e. `{0,...,n-1}`):
```lean
theorem kruskal_katona {r : ℕ} {𝒜 𝒞 : finset (finset X)}
  (h₁ : all_sized 𝒜 r) (h₂ : 𝒜.card = 𝒞.card) (h₃ : is_init_seg_of_colex 𝒞 r) :
(∂𝒞).card ≤ (∂𝒜).card :=
```
We also prove some generalisations: `strengthened` is the same statement, but `h₂` is relaxed to `𝒞.card ≤ 𝒜.card`.

One can also show that the shadow of an initial segment of colex is also an initial segment of colex, so the theorem can be iterated to show that the repeated shadow is also minimsed by colex:
```lean
theorem iterated {r k : ℕ} {𝒜 𝒞 : finset (finset X)}
  (h₁ : all_sized 𝒜 r) (h₂ : 𝒞.card ≤ 𝒜.card) (h₃ : is_init_seg_of_colex 𝒞 r) : 
(shadow^[k] 𝒞).card ≤ (shadow^[k] 𝒜).card :=
``` 

Finally we can get the Kruskal-Katona theorem in the form it was mentioned all the way at the top, provided all the sizes (hidden in the `[...]`) work:
```lean
theorem lovasz_form {r k i : ℕ} {𝒜 : finset (finset X)} [...] 
  (h₁ : all_sized 𝒜 r) (h₂ : choose k r ≤ 𝒜.card) : 
choose k (r-i) ≤ (shadow^[i] 𝒜).card :=
```

Using this, we can prove the Erdős-Ko-Rado theorem. It says that if `A` is a collection of `r`-sets for `r ≤ n/2`, and every two sets in `A` are not disjoint (`A` is _intersecting_), then `A` can't be too large:
```lean
theorem EKR {𝒜 : finset (finset X)} {r : ℕ} 
  (h₁ : intersecting 𝒜) (h₂ : all_sized 𝒜 r) (h₃ : r ≤ n/2) : 
𝒜.card ≤ choose (n-1) (r-1) :=
```

## <a name='Doesntsomeofthisbelonginmathlib'></a>Doesn't some of this belong in mathlib?
Possibly! Some parts might not follow mathlib conventions, although in most places I tried to get reasonably close. 
