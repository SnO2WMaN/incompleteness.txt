#import "template.typ": *

#show: project.with(
  title: "不完全性定理",
  authors: (
    "SnO2WMaN",
  ),
)

#import "@preview/lemmify:0.1.2": *
#let (
  definition, theorem, lemma, corollary, remark, proposition, example, proof, rules: thm-rules
) = default-theorems("thm-group", lang: "en")
#show: thm-rules

#show thm-selector("thm-group", subgroup: "definition"): it => box(
  it,
  stroke: (left: (thickness: 2pt)),
  inset: 1em,
)

#show thm-selector("thm-group", subgroup: "theorem"): it => box(
  it,
  stroke: (left: (thickness: 2pt)),
  inset: 1em,
)

#show thm-selector("thm-group", subgroup: "corollary"): it => box(
  it,
  stroke: (left: (thickness: 2pt)),
  inset: 1em,
)

#show thm-selector("thm-group", subgroup: "proof"): it => box(
  it,
  stroke: (left: (thickness: 2pt, dash: "dotted")),
  inset: 1em,
)


= 計算論

== 準備

#definition(name: "形式的な自然数")[
  TODO
]<formalized_nat>

#let FNat = $mono("N")$
#let vecx = $accent(mono(x), arrow)$

#definition(name: "関係")[
  $n >= 0$に対し，$FNat^n$の部分集合$mono(R) subset.eq FNat^n$を，$n$項関係という．
]<relation>

#let REq = $mono("Eq")$
#let RGt = $mono("Gt")$
#let REven = $mono("Even")$
#example(name: "関係の例")[
  - 「$mono(x)$と$mono(y)$は同数の$mono(s)$を持っている」すなわち「$mono(x)$が$mono(y)$が等しい」という関係$REq$は，2項関係である．$REq = {(mono(0),mono(0)), (mono(1),mono(1)), (mono(2),mono(2)),dots}$．
  - 「$mono(y)$は$mono(x)$より多くの$mono(s)$を持っている」すなわち「$mono(y)$は$mono(x)$より大きい」という関係$RGt$は，2項関係である．$RGt = {(mono(0),mono(1)), (mono(0),mono(2)), (mono(1),mono(3)),dots}$．
  - 偶数の集合は0項関係である．$REven = {mono(0),mono(2),mono(4),...}$．
]<relation_examples>

#definition(name: "特性関数")[
  $n$項関係$mono(R) subset.eq FNat^n$に対し，次の関数$chi_mono(R) : FNat^n -> FNat$を，$mono(R)$の特性関数という．

  $
  chi_mono(R)(vecx) =
  cases(
    mono(1) "if" vecx in mono(R),
    mono(0) "if" vecx in.not mono(R),
  )
  $
]<characteristic_function>

== 原始再帰関数

我々がよく知っている自然数についての初等的な関数の殆どは，原始再帰的な関数として表現できる．

まずは原始再帰的な関数の定義を与えよう．

#let fconst(n,c) = $serif("const")^(#n)_mono(#c)$
#definition(name: "定数関数")[
  $n$個の引数$vecx$を受け取るが，それらを全て破棄して$mono(c)$を返す関数を，定数関数といい，$fconst(n, c) : FNat^n -> FNat$で表す．

  すなわち，$fconst(n,c)(vecx) = mono(c)$である．
]<constant_function>

#let fsucc = $serif("succ")$
#definition(name: "後者関数")[
  受け取った自然数の次の自然数を返す関数を，後者関数といい，$fsucc : FNat -> FNat$で表す．

  すなわち，$fsucc(mono(x)) = mono("s(x)")$である．
]<successor_function>

#let fproj(n,i) = $serif("proj")^(#n)_(#i)$
#definition(name: "射影関数")[
  $n$個の引数$mono(x)_1,...,mono(x)_n$を受け取り，そのうち$i$番目の引数を返す関数を，射影関数といい，$fproj(n,i) : FNat^n -> FNat$で表す．

  すなわち，$fproj(n,i) (mono(x)_1,...,mono(x)_n) = mono(x)_i$である．
]<projection_function>

#let fcomp = $serif("comp")$
#definition(name: "関数合成")[
  $n$変数関数$serif(f) : FNat^n -> FNat$と，$n$個の$m$変数関数$serif(g)_1,...,serif(g)_n : FNat^m -> FNat$が与えられたとき，以下のように定義される$m$変数関数$fcomp_(serif("f"),serif("g")_1,...,serif("g")_n) : FNat^m -> FNat$を，$serif("f"),serif("g")_1,...,serif("g")_n$の関数合成という．
  $ fcomp_(serif("f"),serif("g")_1,...,serif("g")_n)(vecx) = serif("f")(serif("g")_1 (vecx),...,serif("g")_n (vecx)) $
  ここで，$vecx$は$m$個の引数とする．
]<function_composition>

#let fprec(f,g) = $serif("prec")_(#f,#g)$
#definition(name: "原始再帰")[，
  $n$変数関数$serif(f) : FNat^n -> FNat$と，$n+2$変数関数$serif(g) : FNat^(n+2) -> FNat$が与えられたとき，以下のように定義される$n$変数関数$fprec(serif("f"),serif("g")) : FNat^n -> FNat$を，$serif("f"),serif("g")$の原始再帰という．
  $
  fprec(serif("f"),serif("g"))(vecx, mono(0)) &= f(vecx) \
  fprec(serif("f"),serif("g"))(vecx, mono("s(y)")) &= g(vecx, mono(y), serif("prec")_(serif("f"),serif("g"))(vecx, mono("y")))
  $
  ここで，$vecx$は$m$個の引数とする．
]<primitive_recursive>

#definition(name: "原始再帰的関数")[
  ある関数が原始再帰的であるとは，以下のいずれかの条件を満たすことをいう．
  - 定数関数である．
  - 後者関数である．
  - 射影関数である．
  - 原始再帰的な関数による関数合成である．
  - 原始再帰的な関数による原始再帰である．

  原始再帰的な関数を，原始再帰的関数という．
]<primitive_recursive_function>

前述したとおり，自然数についての初等的な関数の殆どが原始再帰的である．見ていこう．

#let fid = $serif("id")$
#definition(name: "恒等関数")[
  $fid : FNat -> FNat := fproj(1, 1)$と定義される関数を，恒等関数とよぶ．
  すなわち，$fid(mono(x)) = mono(x)$である．
]<fzero>

#let fzero(n) = $serif("zero")^#n$
#definition(name: "ゼロ関数")[
  $fzero(n) : FNat^n -> FNat := fconst(n, 0)$と定義される関数を，$n$変数ゼロ関数とよぶ．
  すなわち，$fzero(n)(vecx) = mono(0)$である．
]<fzero>

#let fadd = $serif("add")$
#definition(name: "加算")[
  以下のように定義される関数$fadd : FNat^2 -> FNat$を，加算と呼ぶ．
  $ fadd := fprec(fid,fcomp_(fsucc, fproj(3,3))) $

  合成と原始再帰を外して簡約すると，以下のようになる．
  $
    fadd(mono(x), mono(0)) &= fid(mono(x)) \
    fadd(mono(x), mono("s(y)")) &= fsucc(fproj(3,3)(mono(x), mono(y), fadd(mono(x), mono(y))))
  $

  また，中置記法として，$fadd(x,y)$を$mono(x) + mono(y)$とも書く．
]<add>

#example(name: "加算の例")[
  $fadd$の挙動を確認して，たしかに加算となっていることを確認しよう．

  $fadd(mono(2), mono(3)) = mono(5)$である．
  // #TODO
]<add_example>

#let fmul = $serif("mul")$
#definition(name: "乗算")[
  以下のように定義される関数$fmul : FNat^2 -> FNat$を，乗算と呼ぶ．
  $ fmul := fprec(fzero(1),fcomp_(fadd, fproj(3,1), fproj(3,3))) $

  合成と原始再帰を外して，よりわかりやすく書くと
  $
    fmul(mono(x), mono(0)) &= fzero(1)(mono(x)) \
    fmul(mono(x), mono("s(y)")) &= fadd(fproj(3,1)(mono(x), mono(y), fmul(mono(x), mono(y))), fproj(3,3)(mono(x), mono(y), fmul(mono(x), mono(y))))
  $

  また，中置記法として，$fmul(x,y)$を$mono(x) times mono(y)$とも書く．
]<mul>

#example(name: "乗算の例")[
  $fmul$の挙動を確認して，たしかに乗算となっていることを確認しよう．

  $fadd(mono(2), mono(3)) = mono(6)$である．
  // #TODO
]<mul_example>


#remark(numbering: none)[
  煩雑なので，これより定義する関数では，次のように略記していく．

  - 最も外側の原始再帰は外して定義する．
  - $fconst(n,c), fproj(n,i), fid$は明らかなら省略する．
]

#let fpred = $serif("pred")$
#definition(name: "前者関数")[
  以下のように定義される関数$fpred : FNat -> FNat$を，前者関数と呼ぶ．
  $
    fpred(mono(0)) &= mono(0) \
    fpred(mono("s(x)")) &= fproj(2,1)(mono(x), fpred(mono(x)))
  $
]<pred>

#let fmsub = $serif("msub")$
#definition(name: "補正付き減算")[
  以下のように定義される関数$fmsub : FNat^2 -> FNat$を，補正付き減算と呼ぶ．
  $
    fmsub(mono(x), mono(0)) &= mono(0) \
    fmsub(mono(x), mono("s(y)")) &= fpred(fproj(3,3)(mono(x), mono(y), fmsub(mono(x), mono(y))))
  $

  また，中置記法として，$fmsub(x,y)$を$mono(x) minus.dot mono(y)$とも書く．
]<msub>

#let fbsum(f) = $Sigma_(#f)$
#definition(name: "有界総和")[
  任意の原始再帰関数$serif(f) : FNat^(n+1) -> FNat$について，以下のように定義される関数$fbsum(serif(f)) : FNat^(n+1) -> FNat$を，有界総和と呼ぶ．
  $
    fbsum(serif(f))(vecx, mono(0)) &= serif(f)(vecx, mono(0)) \
    fbsum(serif(f))(vecx, mono("s(y)")) &= serif(f)(vecx, mono("s(y)")) + fbsum(serif(f))(vecx, mono(y))
  $
]<bounded_sum>

#example(name: "有界総和の例")[
  有界総和の例を計算してみよう．
  - $fbsum(fid)(mono(3)) = fid(mono(3)) + fid(mono(2)) + fid(mono(1)) + fid(mono(0)) = mono(6)$
  - $fbsum(fsucc)(mono(3)) = fsucc(mono(3)) + fsucc(mono(2)) + fsucc(mono(1)) + fsucc(mono(0)) = mono(10)$
  - $fbsum(fadd)(mono(2), mono(3)) = fadd(mono(2), mono(3)) + fadd(mono(2), mono(2)) + fadd(mono(2), mono(1)) + fadd(mono(2), mono(0)) = mono(14)$
]

#let fbmul(f) = $Pi_(#f)$
#definition(name: "有界総乗")[
  任意の原始再帰関数$serif(f) : FNat^(n+1) -> FNat$について，以下のように定義される関数$fbmul(serif(f)) : FNat^(n+1) -> FNat$を，有界総和と呼ぶ．
  $
    fbmul(serif(f))(vecx, mono(0)) &= serif(f)(vecx, mono(0)) \
    fbmul(serif(f))(vecx, mono("s(y)")) &= serif(f)(vecx, mono("s(y)")) times fbmul(serif(f))(vecx, mono(y))
  $
]<bounded_mul>

#example(name: "有界総乗の例")[
  有界総乗の例を計算してみよう．
  - $fbmul(fid)(mono(3)) = fid(mono(3)) times fid(mono(2)) times fid(mono(1)) times fid(mono(0)) = mono(0)$
  - $fbmul(fsucc)(mono(3)) = fsucc(mono(3)) times fsucc(mono(2)) times fsucc(mono(1)) times fsucc(mono(0)) = mono(24)$
  - $fbmul(fadd)(mono(2), mono(3)) = fadd(mono(2), mono(3)) times fadd(mono(2), mono(2)) times fadd(mono(2), mono(1)) times fadd(mono(2), mono(0)) = mono(240)$
]

#let fisZero = $serif("isZero")$
#definition(name: "ゼロ判定")[
  以下のように定義される関数$fisZero : FNat -> FNat$を，ゼロ判定と呼ぶ．
  $
    fisZero(mono(0)) &= mono(1) \
    fisZero(mono("s(x)")) &= mono(0)
  $
]<iszero>

#let fisPos = $serif("isPos")$
#definition(name: "正数判定")[
  以下のように定義される関数$fisPos : FNat -> FNat$を，正数判定と呼ぶ．
  $
    fisPos(mono(0)) &= mono(0) \
    fisPos(mono("s(x)")) &= mono(1)
  $
]<iszero>

#definition(name: "原始再帰的関係")[
  関係$mono(R) subset.eq FNat^n$の特性関数$chi_mono(R)$が原始再帰的関数であるとき，$mono(R)$は原始再帰的関係であるという．
]

@relation_examples で見た関係は，いずれも原始再帰的関係である．

#definition(name: "同値関係")[
  $mono(x),mono(y) in FNat$について，「$mono(x)$と$mono(y)$は同数の$mono(s)$を持っている」すなわち「$mono(x)$と$mono(y)$が等しい」という2項関係を同値関係といい，$REq subset.eq FNat^2$として表す．
  $(mono(x),mono(y)) in REq$であることを，$mono(x) = mono(y)$とも書く．
]

#theorem[
  同値関係$REq$は原始再帰的関係である．
]<eq_is_prec>

#proof[
  実際，$chi_mono(REq)(mono(x), mono(y)) = fisZero(mono(x) minus.dot mono(y)) + fisZero(mono(y) minus.dot mono(x))$とすれば要件を満たす．
]

#definition(name: "大小関係")[
  $mono(x),mono(y) in FNat$について，「$mono(y)$は$mono(x)$より多くの$mono(s)$を持っている」すなわち「$mono(y)$は$mono(x)$より大きい」という2項関係を同値関係といい，$RGt subset.eq FNat^2$として表す．
  $(mono(x),mono(y)) in RGt$であることを，$mono(x) < mono(y)$とも書く．
]<gt>

#theorem[
  大小関係$RGt$は原始再帰的関係である．
]<gt_is_prec>

#proof[
  実際，$chi_mono(RGt)(mono(x), mono(y)) = fisPos(mono(y) minus.dot mono(x))$とすれば要件を満たす．
]

偶数の集合が原始再帰的関係であることを示すために，まずはいくつかの論理演算を用意する．

#definition(name: "関係の論理演算")[
  $n$項関係$mono(R),mono(S) subset.eq FNat^n$について，関係$not mono(R), mono(R) and mono(S), mono(R) or mono(S)$を次のように定める．
  - $not mono(R) := {vecx in FNat^n | vecx in.not mono(R)}$．すなわち，「$mono(R)$ではない」という否定．
  - $mono(R) and mono(S) := {vecx in FNat^n | vecx in mono(R) sect mono(S) }$．すなわち，「$mono(R)$かつ$mono(S)$」という連言．
  - $mono(R) or mono(S) := {vecx in FNat^n | vecx in mono(R) union mono(S) }$．すなわち，「$mono(R)$または$mono(S)$」という選言．
]<propositional_logic_operation>

#theorem[
  関係$mono(R),mono(S) subset.eq FNat^n$が原始再帰的関係であるとき，関係$not mono(R), mono(R) and mono(S), mono(R) or mono(S)$も原始再帰的関係である．
]<propositional_logic_operation_prec>

#proof[
  次のように特性関数を定義すれば，論理演算としての要件を満たす．
  - $chi_mono(not mono(R))(vecx) := fisZero(chi_mono(mono(R))(vecx))$
  - $chi_mono(mono(R) and mono(S))(vecx) := chi_mono(mono(R))(vecx) times chi_mono(mono(S))(vecx)$
  - $chi_mono(mono(R) or mono(S))(vecx) := fisPos(chi_mono(mono(R))(vecx) + chi_mono(mono(S))(vecx))$

  このとき定義より$mono(R),mono(S)$の特性関数$chi_mono(R),chi_mono(S)$は原始再帰的関数であるので，$chi_mono(not mono(R)),chi_mono(mono(R) and mono(S)),chi_mono(mono(R) or mono(S))$も原始再帰的関数となる．
]


#let RNEq = $mono("NEq")$
#let RGte = $mono("Gte")$
#definition[
  2項関係$RNEq, RGte$とその略記を，以下のように定める．
  - $RNEq := not REq$とする．すなわち「$mono(x)$と$mono(y)$は等しくない」という関係であり，$mono(x) != mono(y)$とも書く．
  - $RGte := RGt or REq$とする．すなわち「$mono(y)$は$mono(x)$以上」という関係であり，$mono(x) <= mono(y)$とも書く．
]<neq_gte>

#corollary[
  @neq_gte で定義した関係$RNEq, RGte$は，原始再帰的関係である．
]
#proof[
  @eq_is_prec, @gt_is_prec, @propositional_logic_operation_prec より従う．
]

#let RGteForall(y, m, r) = $forall_(#y <= #m).[#r]$
#let RGteExists(y, m, r) = $exists_(#y <= #m).[#r]$
#definition(name: "有界量化")[
  $n + 1$項関係$mono(R) subset.eq FNat^(n + 1)$について，次のような$n+1$項関係を定める．
  - $RGteForall(mono(y), mono(m), mono(R)(vecx, mono(y)))$は「$mono(m)$以下の全ての$mono(y)$で，$mono(R)(vecx, mono(y))$が成立する」を表す関係で，有界全称量化と呼ぶ．
  - $RGteExists(mono(y), mono(m), mono(R)(vecx, mono(y)))$は「$mono(m)$以下のある$mono(y)$で，$mono(R)(vecx, mono(y))$が成立する」を表す関係で，有界存在量化と呼ぶ．

  2つを合わせて，有界量化とも呼ぶ．
]

#remark(numbering: none)[
  自由変数は$vecx, mono(m)$であって，$mono(y)$は束縛変数であることに注意せよ．すなわち，$(vecx, mono(m)) in RGteForall(mono(y), mono(m), mono(R)(vecx, mono(y)))$を確かめているのであって，$(vecx, mono(y)) in RGteForall(mono(y), mono(m), mono(R)(vecx, mono(y)))$ではない．$RGteExists(mono(y), mono(m), mono(R)(vecx, mono(y)))$も同様．
]

#theorem[
  関係$mono(R) subset.eq FNat^n$が原始再帰的関係であるとき，関係$RGteForall(mono(y), mono(m), mono(R)(vecx, mono(y)))$と$RGteExists(mono(y), mono(m), mono(R)(vecx, mono(y)))$は原始再帰的関係である．
]

#proof[
  次のように特性関数を定義すれば，有界量化としての要件を満たす．
  - $chi_mono(RGteForall(mono(y), mono(m), mono(R)(vecx, mono(y))))(vecx) := fbmul(chi_mono(R))(vecx, mono(y)) = chi_mono(R)(vecx, mono(0)) times chi_mono(R)(vecx, mono(1)) times dots.c times chi_mono(R)(vecx, mono(m))$
  - $chi_mono(RGteExists(mono(y), mono(m), mono(R)(vecx, mono(y))))(vecx) := fisPos(fbsum(chi_mono(R))(vecx, mono(y))) = fisPos(chi_mono(R)(vecx, mono(0)) + chi_mono(R)(vecx, mono(1)) + dots.c + chi_mono(R)(vecx, mono(m)))$

  このとき定義より$mono(R)$の特性関数$chi_mono(R)(vecx, mono(y))$が原始再帰的関数であるので，関係$RGteForall(mono(y), mono(m), mono(R)(vecx, mono(y)))$と$RGteExists(mono(y), mono(m), mono(R)(vecx, mono(y)))$も原始再帰的関係である．
]

#remark[
  証明によって構成された特性関数を注意深く観察すれば，有界量化の上界$mono(m)$を何らかの原始再帰関数によって与えても，その特性関数は原始再帰的関数となることがわかる．

  すなわち，$f:FNat^k -> FNat$が原始再帰関数であるなら，$RGteForall(mono(y), f(accent(mono(m), arrow)), mono(R)(vecx, mono(y)))$や$RGteExists(mono(y), f(accent(mono(m), arrow)), mono(R)(vecx, mono(y)))$は原始再帰的な$n + k$項関係となる．
]<bounded_quantification_upper>

便利なので，$<=$を$<$に置き換えた有界量化も定義しておこう．

#let RGtForall(y, m, r) = $forall_(#y < #m).[#r]$
#let RGtExists(y, m, r) = $exists_(#y < #m).[#r]$
#definition[
  $n + 1$項関係$mono(R) subset.eq FNat^(n + 1)$について，次のような関係を定める．
  - $RGtForall(mono(y), mono(m), mono(R)(vecx, mono(y)))$は「$mono(m)$より小さい全ての$mono(y)$で，$mono(R)(vecx, mono(y))$が成立する」を表す関係とする．
  - $RGtExists(mono(y), mono(m), mono(R)(vecx, mono(y)))$は「$mono(m)$より小さいある$mono(y)$で，$mono(R)(vecx, mono(y))$が成立する」を表す関係とする．
]

#corollary[
  関係$mono(R) subset.eq FNat^n$が原始再帰的関係であるとき，関係$RGtForall(mono(y), mono(m), mono(R)(vecx, mono(y)))$と$RGtExists(mono(y), mono(m), mono(R)(vecx, mono(y)))$は原始再帰的関係である．
]

#proof[
  以下のように特性関数を定義すれば要件を満たす．
  - $RGtForall(mono(y), mono(m), mono(R)(vecx, mono(y))) := RGteForall(mono(y), mono(m), mono(R)(vecx, mono(y))) and not mono(R)(vecx, mono(m))$
  - $RGteExists(mono(y), mono(m), mono(R)(vecx, mono(y))) := RGteExists(mono(y), mono(m), mono(R)(vecx, mono(y))) and not mono(R)(vecx, mono(m))$

  これらが原始再帰的関係であることは，@propositional_logic_operation_prec より従う．
]
#remark(numbering: none)[
  @bounded_quantification_upper は$RGtForall(mono(y), mono(m), mono(R)(vecx, mono(y)))$と$RGtExists(mono(y), mono(m), mono(R)(vecx, mono(y)))$についても成り立つ．
  すなわち，上界を何らかの原始再帰関数$f(accent(mono(m), arrow))$によって与えた$RGtForall(mono(y), f(accent(mono(m), arrow)), mono(R)(vecx, mono(y)))$や$RGtExists(mono(y), f(accent(mono(m), arrow)), mono(R)(vecx, mono(y)))$も原始再帰的な$n + k$項関係となる．
]

ここまでの準備によって，偶数の集合が原始再帰的関係であることを示すことができる．

#definition[
  $mono(x) in FNat$について，「$mono(x)$は偶数個の$mono(s)$を持っている」すなわち「$mono(x)$は偶数である」という1項関係を$REven subset.eq FNat$として表す．
]

#corollary[
  関係$REven$は原始再帰的関係である．
]
#proof[
  $REven(mono(x)) := RGteExists(mono(y), mono(x), mono(x) = mono(2) times mono(y))$とすればよい．
]

ここまでの定義で，更に様々な関係が原始再帰的関係として表すことができる．

#let RDiv = $mono("Div")$
#definition[
  $mono(x) in FNat$について，「$mono(x)$は$mono(y)$の約数個の$mono(s)$を持っている」すなわち「$mono(x)$は$mono(y)$で割り切れる」という2項関係を$RDiv subset.eq FNat^2$として表す．
]
#corollary[
  関係$RDiv$は原始再帰的関係である．
]
#proof[
  $RDiv(mono(x),mono(y)) := RGteExists(mono(z), mono(x), mono(x) = mono(y) times mono(z))$とすればよい．
]
#remark(numbering: none)[
  定義より明らかに，$RDiv(mono(x),mono(2))$は$REven$となる．
]

#let RPrime = $mono("Prime")$
#definition[
  $mono(x) in FNat$について，「$mono(x)$は素数個の$mono(s)$を持っている」すなわち「$mono(x)$は素数である」という1項関係を$RPrime subset.eq FNat$として表す．なお，$mono(0), mono(1)$は素数ではないとする．
]
#corollary[
  関係$RPrime$は原始再帰的関係である．
]
#proof[
  $RPrime(mono(x)) := (mono(2) <= mono(x)) and not RGtExists(mono(y), mono(x), mono(y) != mono(1) and RDiv(mono(x), mono(y)))$とすればよい．
]
