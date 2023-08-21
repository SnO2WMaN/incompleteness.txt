#import "template.typ": *

#show: project.with(
  title: "Incompleteness.txt",
  authors: (
    "SnO2WMaN",
  ),
)

#import "@preview/lemmify:0.1.2": *
#let (
  definition, theorem, lemma, corollary, remark, proposition, example, proof, rules: thm-rules
) = default-theorems("thm-group", lang: "en", max-reset-level: 3)

#show: thm-rules
#show thm-selector("thm-group", subgroup: "definition"): it => box(
  it,
  stroke: (left: (thickness: 2pt)),
  inset: 1em,
)
#show thm-selector("thm-group", subgroup: "theorem"): it => box(
  it,
  stroke: 1pt,
  inset: 1em
)
#show thm-selector("thm-group", subgroup: "lemma"): it => box(
  it,
  stroke: (thickness: 1pt, dash: "dotted"),
  inset: 1em
)
#show thm-selector("thm-group", subgroup: "corollary"): it => box(
  it,
  stroke: 1pt,
  inset: 1em
)
#show thm-selector("thm-group", subgroup: "example"): it => box(
  it,
  inset: (left: 1em, right: 1em, top: 1em, bottom: 1em),
)
#show thm-selector("thm-group", subgroup: "remark"): it => box(
  it,
  inset: (left: 1em, right: 1em, top: 1em, bottom: 1em),
)
#show thm-selector("thm-group", subgroup: "proof"): it => box(
  it,
  stroke: (left: (thickness: 1pt, dash: "dotted")),
  inset: (left: 1em, right: 1em, top: 0.5em, bottom: 0.5em),
)

#show outline.entry.where(
  level: 1
): it => {
  v(1em, weak: true)
  strong(it)
}
#outline(indent: auto)

#let TODO(content) = emph("TODO:" + content)

#let Theory(a) = $upright(sans(#a))$
#let PeanoArithmetic = $Theory("PA")$
#let RobinsonArithmetic = $Theory("Q")$
#let WeakestArithmetic = $Theory("R")$

#let Language = $cal("L")$
#let ArithmeticLanguage = $Language_sans("A")$

#let Nat = $bb("N")$
#let Nat2Nat(n) = $Nat^#n -> Nat$
#let vec(x) = $accent(#x, arrow)$
#let vecx = $vec(x)$
#let vecy = $vec(y)$

#let charFn(R) = $chi_(#R)$

#let succ = $serif("s")$

#let fn(txt) = $upright(serif(txt))$
#let fnConst(n,c) = $fn("const")^(#n)_(#c)$
#let fnSucc = $fn("succ")$
#let fnProj(n,i) = $fn("proj")^(#n)_(#i)$
#let fnComp = $fn("comp")$
#let fnPrec(f,g) = $fn("prec")_(#f,#g)$
#let fnZero(n) = $fn("zero")^#n$
#let fnId = $fn("id")$
#let fnAdd = $fn("add")$
#let fnMul = $fn("mul")$
#let fnExp = $fn("exp")$
#let fnFrac = $fn("frac")$
#let fnPred = $fn("pred")$
#let fnMsub = $fn("msub")$
#let fnIsZero = $fn("iszero")$
#let fnIsPos = $fn("ispos")$
#let fnBSum(f) = $Sigma_(#f)$
#let fnBMul(f) = $Pi_(#f)$
#let fnBCase(R,f,g) = $"if" #R "then" #f "else" #g$
#let fnBMinimize(y, m, R) = $mu_(#y <= #m).[#R]$
#let fnPrime = $fn("pr")$

#let Rel(txt) = $upright(serif(txt))$
#let REq = $Rel("Eq")$
#let RGt = $Rel("Gt")$
#let REven = $Rel("Even")$
#let RNEq = $Rel("NEq")$
#let RGte = $Rel("Gte")$
#let RDiv = $Rel("Div")$
#let RPrime = $Rel("Prime")$
#let RGteForall(y, m, r) = $forall_(#y <= #m).[#r]$
#let RGteExists(y, m, r) = $exists_(#y <= #m).[#r]$
#let RGtForall(y, m, r) = $forall_(#y < #m).[#r]$
#let RGtExists(y, m, r) = $exists_(#y < #m).[#r]$

#let GoedelNum(x) = $lr(⸢#x⸣)$ // $⸢#x⸣$ // $attach(#x, tl: "⸢", tr: "⸣")$ // $⌜#x⌝$ //  $attach(#x, tl: "⌜", tr: "⌝")$
#let NumTerm(x) = $overline(#x)$
#let GoedelNumTerm(x) = $NumTerm(GoedelNum(#x))$

#let GoedelSentence = $serif("G")$
#let RosserSentence = $serif("R")$
#let HenkinSentence = $serif("H")$
#let JeroslowSentence = $serif("J")$

#let Provability(T, lt: none, content) = $serif("Pr")^(#lt)_(#T)(content)$
#let RosserProvability(T, content) = $Provability(#T, lt: serif("Ro"), #content)$
#let Consistency(T, lt: none) = $serif("Con")^(#lt)_#T$
#let RosserConsistency(T) = $Consistency(#T, lt: serif("Ro"))$

#let Drv1 = $bold(serif("D1"))$
#let Drv2 = $bold(serif("D2"))$
#let Drv3 = $bold(serif("D3"))$

#let proves = symbol(
  "\u{22A2}",
  ("not", "\u{22AC}")
)
#let models = symbol(
  "\u{22A8}",
  ("not", "\u{22AD}")
)

#let iff = $<==>$

#let TheoryT = $T$
#let TheoryU = $U$

#let StandardArithmeticModel = $cal(N)$

= はじめに

この文書は不完全性定理についての諸々をまとめたものです．
自分用に纏めたものであり，人に見せることをあまり想定していないので，説明が不十分な部分があるかもしれません．
また普通に誤りがある可能性もあります．
これらの点についてはご了承ください．

== メタ情報

- この文書は#link("https://typst.app")[Typst]という執筆時では新興の組版システムによって作成しています．
- 文書のソースファイル等は#link("https://github.com/SnO2WMaN/incompleteness.txt")に置かれており，最新のPDFファイルが自動的に#link("https://sno2wman.github.io/incompleteness.txt/main.pdf")にデプロイされています#footnote[文書のコンパイルが失敗していなければ．]．
- 文書のライセンスは#link("https://github.com/SnO2WMaN/incompleteness.txt/blob/main/LICENSE")[CC0 1.0]であり，可能な限り著作権を放棄します．
- 誤りなどがあれば，#link("https://github.com/SnO2WMaN/incompleteness.txt/issues")[GitHubのissue]か著者に連絡していただけると助かります．

== 読書案内

日本語で書かれた不完全性定理についての文献としては#cite("kikuchi_2014", "kurahashi_2021", "smullyan_1992_ja","kikuchi_sano_kurahashi_usuba_kurokawa_2016")があります．
知っている範囲で簡単に紹介しておきます．#TODO[もっとちゃんと文献を増やす]

- #cite("kikuchi_2014")は，日本における不完全性定理の第一人者#footnote[少なくとも私はそう思っています．]による不完全性定理の証明に至るまでの丁寧な解説書であり，更に少しの発展的な話題も載っています．数学の哲学について禁欲でないという特徴もあります．
- #cite("kurahashi_2021")は，示すこと自体が目標になりがちな不完全性定理の，更に発展的な話題について書かれています．ただし，紙面の都合で多くの定理の証明が載っていません．
- #cite("smullyan_1992_ja")は#cite("smullyan_1992")の日本語訳です．私が最初に読んだという点で思い入れがありますが，用語やアプローチがかなり独特なので，入門としてはあまりおすすめはしません#footnote[事情としては，Smullyanが数論的なアプローチを避けてより初等的な形式での議論を行おうとしている気があり，不完全性定理について全く知らない人間にとってはどういうモチベーションでそんなことをしているのか分かりにくいという難点があります．逆に言えば，分かってしまえばむしろかなり丁寧に議論していることが分かります．]．
- #cite("kikuchi_sano_kurahashi_usuba_kurokawa_2016")は大きく様相論理，証明可能性論理，強制法，真理論についての本です．不完全性定理については，証明可能性論理の節で扱われています．

英語で書かれた文献はもっとあります．#TODO[もっと書く]

== 更新履歴

#TODO[一旦完成してから書く．]

= パラドックス！

= 不完全性定理とは何なのか？

// ここの歴史はかなり疑わしい

今日「不完全性定理」と呼ばれる定理は，Gödel#cite("goedel_1931")によって初めて証明された．
この元論文#cite("goedel_1931")ではRussel,WhiteheadによるPrincipia MathematicaをGödelがより使いやすく改良した体系における第1不完全性定理の証明が与えられ，第2不完全性定理についてはそのスケッチのみを与えるに留まっている．
第2不完全性定理の詳細な証明については#cite("hilbert_bernays_1939")によって最初に証明が与えられた．

== 不完全性定理という名前について

#cite("tanaka_2012", "fuchino_2013")参照．

= 計算論

== 準備

#TODO[どういうモチベーションで #ref(<formalized_nat>)を導入しているかをちゃんと書く]

#definition(name: "形式的な自然数")[
  // あとで書く．
]<formalized_nat>

#definition(name: "関数")[
  // あとで書く．
]


#definition(name: "関係")[
  $n >= 0$に対し，$Nat^n$の部分集合$Rel(R) subset.eq Nat^n$を，$n$項関係という．
]<relation>

#example(name: "関係の例")[
  - 「$x$と$y$は同数の$Rel(S)$を持っている」すなわち「$x$が$y$が等しい」という関係$REq$は，2項関係である．$REq = {(0,0), (1,1), (2,2),dots}$．
  - 「$y$は$x$より多くの$Rel(S)$を持っている」すなわち「$y$は$x$より大きい」という関係$RGt$は，2項関係である．$RGt = {(0,1), (0,2), (1,3),dots}$．
  - 偶数の集合は1項関係である．$REven = {0,2,4,...}$．
]<relation_examples>

#definition(name: "特性関数")[
  $n$項関係$Rel(R) subset.eq Nat^n$に対し，次の関数$charFn(Rel(R)) : Nat2Nat(n)$を，$Rel(R)$の特性関数という．

  $
  charFn(Rel(R))(vecx) =
  cases(
    1 "if" vecx in Rel(R),
    0 "if" vecx in.not Rel(R),
  )
  $
]<characteristic_function>

// 部分集合というものをそのまま経由せず，特性関数という関数に依って特徴づけられる$Nat^n$の部分集合を関係と呼ぶ，のように定義した方が良い気もする．

== 原始再帰的

我々のよく知っている自然数についての初等的な関数や関係の殆どは，原始再帰的な関数や関係として表現できる．

まずは原始再帰的な関数の定義を与えよう．

#definition(name: "定数関数")[
  $n$個の引数$vecx$を受け取るが，それらを全て破棄して$c$を返す関数を，定数関数といい，$fnConst(n, c) : Nat2Nat(n)$で表す．

  すなわち，$fnConst(n,c)(vecx) = c$である．
]<Computability_ConstFunction>

#definition(name: "後者関数")[
  受け取った自然数の次の自然数を返す関数を，後者関数といい，$fnSucc : Nat2Nat(1)$で表す．

  すなわち，$fnSucc(x) = succ(x)$である．
]<Computability_SuccFunction>

#definition(name: "射影関数")[
  $n$個の引数$x_1,...,x_n$を受け取り，そのうち$i$番目の引数を返す関数を，射影関数といい，$fnProj(n,i) : Nat2Nat(n)$で表す．

  すなわち，$fnProj(n,i) (x_1,...,x_n) = x_i$である．
]<Computability_ProjectionFunction>

#definition(name: "関数合成")[
  $n$変数関数$fn(f) : Nat2Nat(n)$と，$n$個の$m$変数関数$fn(g)_1,...,fn(g)_n : Nat2Nat(m)$が与えられたとき，以下のように定義される$m$変数関数$fnComp_(fn(f),fn(g)_1,...,fn(g)_n) : Nat2Nat(m)$を，$fn(f),fn(g)_1,...,fn(g)_n$の関数合成という．
  $ fnComp_(fn(f),fn(g)_1,...,fn(g)_n)(vecx) = fn(f)(fn(g)_1 (vecx),...,fn(g)_n (vecx)) $
  ここで，$vecx$は$m$個の引数とする．
]<Computability_FunctionComposition>

#definition(name: "原始再帰")[，
  $n$変数関数$fn(f) : Nat2Nat(n)$と，$n+2$変数関数$fn(g) : Nat2Nat(n+2)$が与えられたとき，以下のように定義される$n$変数関数$fnPrec(fn(f),fn(g)) : Nat2Nat(n)$を，$fn(f),fn(g)$の原始再帰という．
  $
  fnPrec(fn(f),fn(g))(vecx, 0) &= fn(f)(vecx) \
  fnPrec(fn(f),fn(g))(vecx, succ(y)) &= fn(g)(vecx, y, fnPrec(fn(f),fn(g))(vecx, y))
  $
  ここで，$vecx$は$m$個の引数とする．
]<Computability_PrimitiveRecursive>

#definition(name: "原始再帰的関数")[
  ある関数が原始再帰的であるとは，以下のいずれかの条件を満たすことをいう．
  - 定数関数である．(#ref(<Computability_ConstFunction>))
  - 後者関数である．(#ref(<Computability_SuccFunction>))
  - 射影関数である．(#ref(<Computability_ProjectionFunction>))
  - 原始再帰的な関数による関数合成である．(#ref(<Computability_FunctionComposition>))
  - 原始再帰的な関数による原始再帰である．(#ref(<Computability_PrimitiveRecursive>))

  原始再帰的な関数を，原始再帰的関数という．
]<Computability_PrimitiveRecursiveFunction>

=== 原始再帰的関数の例

前述したとおり，自然数についての初等的な関数の殆どが原始再帰的である．見ていこう．

#definition(name: "恒等関数")[
  $fnId : Nat2Nat(1) := fnProj(1, 1)$と定義される関数を，恒等関数とよぶ．
  すなわち，$fnId(x) = x$である．
]<Computability_IdFunction>

#definition(name: "ゼロ関数")[
  $fnZero(n) : Nat2Nat(n) := fnConst(n, 0)$と定義される関数を，$n$変数ゼロ関数とよぶ．
  すなわち，$fnZero(n)(vecx) = 0$である．
]<Computability_ZeroFunction>

#definition(name: "加算")[
  以下のように定義される関数$fnAdd : Nat2Nat(2)$を，加算と呼ぶ．
  $ fnAdd := fnPrec(fnId,fnComp_(fnSucc, fnProj(3,3))) $

  合成と原始再帰を外して簡約すると，以下のようになる．
  $
    fnAdd(x, 0) &= fnId(x) \
    fnAdd(x, succ(y)) &= fnSucc(fnProj(3,3)(x, y, fnAdd(x, y)))
  $

  また，中置記法として，$fnAdd(x,y)$を$x + y$とも書く．
]<Computability_AddFunction>

#example(name: "加算の例")[
  $fnAdd$の挙動を確認して，たしかに加算となっていることを確認しよう．

  $fnAdd(2, 3) = 5$である．
  // #TODO
]

#definition(name: "乗算")[
  以下のように定義される関数$fnMul : Nat2Nat(2)$を，乗算と呼ぶ．
  $ fnMul := fnPrec(fnZero(1),fnComp_(fnAdd, fnProj(3,1), fnProj(3,3))) $

  合成と原始再帰を外して，よりわかりやすく書くと
  $
    fnMul(x, 0) &= fnZero(1)(x) \
    fnMul(x, succ(y)) &= fnAdd(fnProj(3,1)(x, y, fnMul(x, y)), fnProj(3,3)(x, y, fnMul(x, y)))
  $

  また，中置記法として，$fnMul(x,y)$を$x times y$とも書く．
]<Computability_MulFunction>

#example(name: "乗算の例")[
  $fnMul$の挙動を確認して，たしかに乗算となっていることを確認しよう．

  $fnAdd(2, 3) = 6$である．
  // #TODO
]

ここまで定義した関数について，定義より明らかに次の #ref(<Computability_PrimRecFn1>)が成り立つ．

#corollary[
  恒等関数$fnId$，ゼロ関数$fnZero$，加算$fnAdd$，乗算$fnMul$は原始再帰的関数である．
]<Computability_PrimRecFn1>

さて，更に関数を定義していきたいが，毎回#ref(<Computability_AddFunction>)や#ref(<Computability_MulFunction>)のように愚直に全ての関数を書き下していくと，あまりにも煩雑になってしまう．
これを避けるために，#ref(<Computability_PrimRecFnAbbrev>)を導入する．

#remark[
  以下の略記を用いてもよいとする．
  - 最も外側の原始再帰は外して定義する．
  - $fnConst(n,c), fnProj(n,i), fnId$は明らかなら省略する．
]<Computability_PrimRecFnAbbrev>

#definition(name: "冪乗")[
  以下のように定義される関数$fnExp : Nat2Nat(2)$を，冪乗と呼ぶ．
  $
    fnExp(x, 0) &= 1 \
    fnExp(x, succ(x)) &= x times fnExp(x, y)
  $
  また，略記として$fnExp(x,y)$を$x^y$とも書く．
]<Computability_ExpFunction>

#definition(name: "階乗")[
  以下のように定義される関数$fnFrac : Nat2Nat(1)$を，冪乗と呼ぶ．
  $
    fnFrac(0) &= 1 \
    fnFrac(succ(x)) &= (x + 1) times fnFrac(x)
  $
  また，略記として$fnFrac(x)$を$x!$とも書く．
]<Computability_FracFunction>

#definition(name: "前者関数")[
  以下のように定義される関数$fnPred : Nat2Nat(1)$を，前者関数と呼ぶ．
  $
    fnPred(0) &= 0 \
    fnPred(succ(x)) &= fnProj(2,1)(x, fnPred(x))
  $
]<Computability_PredFunction>

#definition(name: "補正付き減算")[
  以下のように定義される関数$fnMsub : Nat2Nat(2)$を，補正付き減算と呼ぶ．
  $
    fnMsub(x, 0) &= 0 \
    fnMsub(x, succ(y)) &= fnPred(fnMsub(x, y))
  $
  また，中置記法として，$fnMsub(x,y)$を$x minus.dot y$とも書く．
]<Computability_MSubFunction>

後で特性関数を定義するときに必要となる，次の関数も定義しておこう．

#definition(name: "ゼロ判定")[
  以下のように定義される関数$fnIsZero : Nat2Nat(1)$を，ゼロ判定と呼ぶ．
  $
    fnIsZero(0) &= 1 \
    fnIsZero(succ(x)) &= 0
  $
]<Computability_IsZeroFunction>

#definition(name: "正数判定")[
  以下のように定義される関数$fnIsPos : Nat2Nat(1)$を，正数判定と呼ぶ．
  $
    fnIsPos(0) &= 0 \
    fnIsPos(succ(x)) &= 1
  $
]<Computability_IsPosFunction>

ここまで定義した関数についても，やはり明らかに次の #ref(<Computability_PrimRecFn2>)が成り立つ．

#corollary[
  冪乗$fnExp$，階乗$fnFrac$，前者関数$fnPred$，補正付き減算$fnMsub$，ゼロ判定$fnIsZero$，正数判定$fnIsPos$は原始再帰的関数である．
]<Computability_PrimRecFn2>

#definition(name: "有界総和")[
  関数$fn(f) : Nat2Nat(n+1)$について，以下のように定義される関数$fnBSum(fn(f)) : Nat2Nat(n+1)$を，有界総和と呼ぶ．
  $
    fnBSum(fn(f))(vecx, 0) &= fn(f)(vecx, 0) \
    fnBSum(fn(f))(vecx, succ(y)) &= fn(f)(vecx, succ(y)) + fnBSum(fn(f))(vecx, y)
  $
]<Computability_BoundedSumFunction>

#example(name: "有界総和の例")[
  有界総和の例を計算してみよう．
  - $fnBSum(fnId)(3) = fnId(3) + fnId(2) + fnId(1) + fnId(0) = 6$
  - $fnBSum(fnSucc)(3) = fnSucc(3) + fnSucc(2) + fnSucc(1) + fnSucc(0) = 10$
  - $fnBSum(fnAdd)(2, 3) = fnAdd(2, 3) + fnAdd(2, 2) + fnAdd(2, 1) + fnAdd(2, 0) = 14$
]

#definition(name: "有界総乗")[
  関数$fn(f) : Nat2Nat(n+1)$について，以下のように定義される関数$fnBMul(fn(f)) : Nat2Nat(n+1)$を，有界総乗と呼ぶ．
  $
    fnBMul(fn(f))(vecx, 0) &= fn(f)(vecx, 0) \
    fnBMul(fn(f))(vecx, succ(y)) &= fn(f)(vecx, succ(y)) times fnBMul(fn(f))(vecx, y)
  $
]<Computability_BoundedMulFunction>

#example(name: "有界総乗の例")[
  有界総乗の例を計算してみよう．
  - $fnBMul(fnId)(3) = fnId(3) times fnId(2) times fnId(1) times fnId(0) = 0$
  - $fnBMul(fnSucc)(3) = fnSucc(3) times fnSucc(2) times fnSucc(1) times fnSucc(0) = 24$
  - $fnBMul(fnAdd)(2, 3) = fnAdd(2, 3) times fnAdd(2, 2) times fnAdd(2, 1) times fnAdd(2, 0) = 240$
]

有界総和と有界総乗についても自明に次の #ref(<Computability_PrimRecFn3>)が成り立つ．

#corollary[
  $f: Nat2Nat(n+1)$が原始再帰的関数であるなら，有界総和$fnBSum(f)$，有界総乗$fnBMul(f)$は原始再帰的関数である．
]<Computability_PrimRecFn3>

=== 原始再帰的関係

#definition(name: "原始再帰的関係")[
  関係$Rel(R) subset.eq Nat^n$の特性関数$charFn(Rel(R))$が原始再帰的関数であるとき，$Rel(R)$は原始再帰的関係であるという．
]

#ref(<relation_examples>)で見た関係は，いずれも原始再帰的関係である．

#definition(name: "同値関係")[
  $x,y in Nat$について，「$x$と$y$は同数の$Rel(S)$を持っている」すなわち「$x$と$y$が等しい」という2項関係を同値関係といい，$REq subset.eq Nat^2$として表す．
  $(x,y) in REq$であることを，$x = y$とも書く．
]<Computability_REq>

#theorem[
  同値関係$REq$は原始再帰的関係である．
]<Computability_ReqIsPrimRec>

#proof[
  実際，$charFn(REq)(x, y) = fnIsZero(x minus.dot y) + fnIsZero(y minus.dot x)$とすれば要件を満たす．
]

#definition(name: "大小関係")[
  $x,y in Nat$について，「$y$は$x$より多くの$Rel(S)$を持っている」すなわち「$y$は$x$より大きい」という2項関係を同値関係といい，$RGt subset.eq Nat^2$として表す．
  $(x,y) in RGt$であることを，$x < y$とも書く．
]<Computability_RGt>

#theorem[
  大小関係$RGt$は原始再帰的関係である．
]<Computability_RGtIsPrimRec>

#proof[
  実際，$charFn(RGt)(x, y) = fnIsPos(y minus.dot x)$とすれば要件を満たす．
]

偶数の集合が原始再帰的関係であることを示すために，まずはいくつかの論理演算を用意する．

#definition(name: "関係の論理演算")[
  $n$項関係$Rel(R),Rel(S) subset.eq Nat^n$について，関係$not Rel(R), Rel(R) and Rel(S), Rel(R) or Rel(S)$を次のように定める．
  - $not Rel(R) := {vecx in Nat^n | vecx in.not Rel(R)}$．すなわち，「$Rel(R)$ではない」という否定．
  - $Rel(R) and Rel(S) := {vecx in Nat^n | vecx in Rel(R) sect Rel(S) }$．すなわち，「$Rel(R)$かつ$Rel(S)$」という連言．
  - $Rel(R) or Rel(S) := {vecx in Nat^n | vecx in Rel(R) union Rel(S) }$．すなわち，「$Rel(R)$または$Rel(S)$」という選言．
]<Computability_RelLogicOperation>

#theorem[
  関係$Rel(R),Rel(S) subset.eq Nat^n$が原始再帰的関係であるとき，関係$not Rel(R), Rel(R) and Rel(S), Rel(R) or Rel(S)$も原始再帰的関係である．
]<Computability_RelLogicOperationIsPrimRec>

#proof[
  次のように特性関数を定義すれば，論理演算としての要件を満たす．
  - $charFn(not Rel(R))(vecx) := fnIsZero(charFn(Rel(R))(vecx))$
  - $charFn(Rel(R) and Rel(S))(vecx) := charFn(Rel(R))(vecx) times charFn(Rel(S))(vecx)$
  - $charFn(Rel(R) or Rel(S))(vecx) := fnIsPos(charFn(Rel(R))(vecx) + charFn(Rel(S))(vecx))$

  このとき仮定より$Rel(R),Rel(S)$の特性関数$charFn(Rel(R)),chi_Rel(S)$は原始再帰的関数であるので，#ref(<Computability_PrimRecFn1>)や #ref(<Computability_PrimRecFn2>)より，$charFn(not Rel(R)),charFn(Rel(R) and Rel(S)),charFn(Rel(R) or Rel(S))$も原始再帰的関数となる．
]

#remark(numbering: none)[
  $Rel(R) and Rel(S), Rel(R) or Rel(S)$の特性関数$charFn(Rel(R) and Rel(S))(vecx), charFn(Rel(R) or Rel(S))(vecx)$を観察すると，前者は乗算，後者は加算に基づいて特性関数が構成されている．このような対応から，連言と選言はそれぞれ論理積と論理和とも呼ばれる．
]

#definition[
  2項関係$RNEq, RGte$とその略記を，以下のように定める．
  - $RNEq := not REq$とする．すなわち「$x$と$y$は等しくない」という関係であり，$x != y$とも書く．
  - $RGte := RGt or REq$とする．すなわち「$y$は$x$以上」という関係であり，$x <= y$とも書く．
]

#ref(<Computability_RelLogicOperationIsPrimRec>)などより明らかに，次の系が成り立つ．

#corollary[
  関係$RNEq, RGte$は，原始再帰的関係である．
]

#definition(name: "有界量化")[
  $n + 1$項関係$Rel(R) subset.eq Nat^(n + 1)$について，次のような$n+1$項関係を定める．
  - $RGteForall(y, m, Rel(R)(vecx, y))$は「$m$以下の全ての$y$で，$Rel(R)(vecx, y)$が成立する」を表す関係で，有界全称量化と呼ぶ．
  - $RGteExists(y, m, Rel(R)(vecx, y))$は「$m$以下のある$y$で，$Rel(R)(vecx, y)$が成立する」を表す関係で，有界存在量化と呼ぶ．

  2つを合わせて，有界量化とも呼ぶ．
]

#remark(numbering: none)[
  自由変数は$vecx, m$であって，$y$は束縛変数であることに注意せよ．すなわち，$(vecx, m) in RGteForall(y, m, Rel(R)(vecx, y))$を確かめているのであって，$(vecx, y) in RGteForall(y, m, Rel(R)(vecx, y))$ではない．$RGteExists(y, m, Rel(R)(vecx, y))$も同様．
]

#theorem[
  関係$Rel(R) subset.eq Nat^n$が原始再帰的関係であるとき，関係$RGteForall(y, m, Rel(R)(vecx, y))$と$RGteExists(y, m, Rel(R)(vecx, y))$は原始再帰的関係である．
]

#proof[
  次のように特性関数を定義すれば，有界量化としての要件を満たす．
  - $charFn(RGteForall(y, m, Rel(R)(vecx, y)))(vecx) := fnBMul(charFn(Rel(R)))(vecx, y) = charFn(Rel(R))(vecx, 0) times charFn(Rel(R))(vecx, 1) times dots.c times charFn(Rel(R))(vecx, m)$
  - $charFn(RGteExists(y, m, Rel(R)(vecx, y)))(vecx) := fnIsPos(fnBSum(charFn(Rel(R)))(vecx, y)) = fnIsPos(charFn(Rel(R))(vecx, 0) + charFn(Rel(R))(vecx, 1) + dots.c + charFn(Rel(R))(vecx, m))$

  このとき定義より$Rel(R)$の特性関数$charFn(Rel(R))(vecx, y)$が原始再帰的関数であるので，関係$RGteForall(y, m, Rel(R)(vecx, y))$と$RGteExists(y, m, Rel(R)(vecx, y))$も原始再帰的関係である．
]

#remark[
  証明によって構成された特性関数を注意深く観察すれば，有界量化の上界$m$を何らかの原始再帰関数によって与えても，その特性関数は原始再帰的関数となることがわかる．
  すなわち，$f:Nat2Nat(k)$が原始再帰関数であるなら，$RGteForall(y, fn(f)(accent(m, arrow)), Rel(R)(vecx, y))$や$RGteExists(y, fn(f)(accent(m, arrow)), Rel(R)(vecx, y))$は原始再帰的な$n + k$項関係となる．
]<Computability_BoundedQuantificationUpperRemark>

便利なので，$<=$を$<$に置き換えた有界量化も定義しておこう．

#definition[
  $n + 1$項関係$Rel(R) subset.eq Nat^(n + 1)$について，次のような関係を定める．
  - $RGtForall(y, m, Rel(R)(vecx, y))$は「$m$より小さい全ての$y$で，$Rel(R)(vecx, y)$が成立する」を表す関係とする．
  - $RGtExists(y, m, Rel(R)(vecx, y))$は「$m$より小さいある$y$で，$Rel(R)(vecx, y)$が成立する」を表す関係とする．
]

#theorem[
  関係$Rel(R) subset.eq Nat^n$が原始再帰的関係であるとき，関係$RGtForall(y, m, Rel(R)(vecx, y))$と$RGtExists(y, m, Rel(R)(vecx, y))$は原始再帰的関係である．
]

#proof[
  以下のように特性関数を定義すれば要件を満たす．
  - $RGtForall(y, m, Rel(R)(vecx, y)) := RGteForall(y, m, Rel(R)(vecx, y)) and not Rel(R)(vecx, m)$
  - $RGteExists(y, m, Rel(R)(vecx, y)) := RGteExists(y, m, Rel(R)(vecx, y)) and not Rel(R)(vecx, m)$

  これらが原始再帰的関係であることは，#ref(<Computability_RelLogicOperationIsPrimRec>)より従う．
]

#remark(numbering: none)[
  #ref(<Computability_BoundedQuantificationUpperRemark>)は$RGtForall(y, m, Rel(R)(vecx, y))$と$RGtExists(y, m, Rel(R)(vecx, y))$についても成り立つ．
  すなわち，上界を何らかの原始再帰関数$fn(f)(accent(m, arrow))$によって与えた$RGtForall(y, fn(f)(accent(m, arrow)), Rel(R)(vecx, y))$や$RGtExists(y, fn(f)(accent(m, arrow)), Rel(R)(vecx, y))$もやはり原始再帰的な$n + k$項関係となる．
]

ここまでの準備によって，偶数の集合が原始再帰的関係であることを示すことができる．

#definition[
  $x in Nat$について，「$x$は偶数個の$Rel(S)$を持っている」すなわち「$x$は偶数である」という1項関係を$REven subset.eq Nat$として表す．
]

#theorem[
  関係$REven$は原始再帰的関係である．
]

#proof[
  $REven(x) := RGteExists(y, x, x = 2 times y)$とすればよい．
]

更に様々な関係も原始再帰的関係として表すことができる．

#definition[
  $x in Nat$について，「$x$は$y$の約数個の$Rel(S)$を持っている」すなわち「$x$は$y$で割り切れる」という2項関係を$RDiv subset.eq Nat^2$として表す．
]

#theorem[
  関係$RDiv$は原始再帰的関係である．
]

#proof[
  $RDiv(x,y) := RGteExists(z, x, x = y times z)$とすればよい．
]

#remark(numbering: none)[
  定義より明らかに，$RDiv(x,2)$は$REven$となる．
]

#definition[
  $x in Nat$について，「$x$は素数個の$Rel(S)$を持っている」すなわち「$x$は素数である」という1項関係を$RPrime subset.eq Nat$として表す．なお，$0, 1$は素数ではないとする．
]

#theorem[
  関係$RPrime$は原始再帰的関係である．
]<Computability_RPrimeIsPrimRec>

#proof[
  $RPrime(x) := (2 <= x) and not RGtExists(y, x, y != 1 and RDiv(x, y))$とすればよい．
]

=== 場合分け関数と有界最小化

#definition(name: "場合分け関数")[
  関係$Rel(R) subset.eq Nat^n$と関数$fn(f), fn(g) : Nat2Nat(n)$について，以下のように定義される関数$(fnBCase(Rel(R), fn(f), fn(g))) : Nat2Nat(n)$を，場合分け関数と呼ぶ．
  $
    (fnBCase(Rel(R), fn(f), fn(g)))(vecx) := cases(
      fn(f)(vecx) "if" vecx in Rel(R),
      fn(g)(vecx) "if" vecx in.not Rel(R)
    )
  $

  煩雑な場合は，$(fnBCase(Rel(R), fn(f), fn(g)))(vecx)$を$fnBCase(Rel(R)(vecx), fn(f)(vecx), fn(g)(vecx))$とも略記する．
]

#theorem[
  関係$Rel(R) subset.eq Nat^n$が原始再帰的関係，関数$fn(f), fn(g) : Nat2Nat(n)$が原始再帰的関数であるとき，関数$(fnBCase(Rel(R), fn(f), fn(g))) : Nat2Nat(n)$も原始再帰的関数である．
]

#proof[
  $(fnBCase(Rel(R), fn(f), fn(g)))(vecx) := charFn(Rel(R))(vecx) times fn(f)(vecx) + chi_(not Rel(R))(vecx) times fn(g)(vecx)$と定義すれば要件を満たし，これが原始再帰的関数になることは明らか．
]

#let textm(content) = text(font: "Noto Serif CJK JP", weight: "regular", content)

#definition(name: "有界最小化関数")[
  $n+1$項関係$Rel(R) subset.eq Nat^(n + 1)$に対し，以下のように定義される$n+1$項関数$fnBMinimize(y, m, Rel(R)(vecx, y)) : Nat2Nat(n+1)$を，有界最小化関数と呼ぶ．
  $
    fnBMinimize(y, m, Rel(R)(vecx, y)) :=
    cases(
      k quad #textm[$m$以下の$y$のうち，$Rel(R)(vecx, y)$を成立させる最小の$y$が$k$として存在するとき],
      m quad #textm[そのような$y$が存在しないとき]
    )
  $
]

#theorem[
  関係$Rel(R) subset.eq Nat^(n + 1)$が原始再帰的関係であるとき，有界最小化関数$fnBMinimize(y, m, Rel(R)(vecx, y)) : Nat2Nat(n+1)$は原始再帰的関数である．
]

#proof[
  以下のように定義すれば要件を満たす．
  $
    fnBMinimize(y, 0, Rel(R)(vecx, y)) &= 0 \
    fnBMinimize(y, s(m), Rel(R)(vecx, y)) &= fnBCase(RGteExists(y, m, Rel(R)(vecx, y)) , fnBMinimize(y, m, Rel(R)(vecx, y)), s(m))
  $

  これが原始再帰的関数になることは明らか．
]

#remark[
  この証明で構成した関数をよく見れば，やはり#ref(<Computability_BoundedQuantificationUpperRemark>)はここでも適用できることがわかる．すなわち，有界最小化の上界を何らかの原始再帰関数$f:Nat2Nat(k)$によって与えた$fnBMinimize(y, fn(f)(accent(m, arrow)), Rel(R)(vecx, y))$も，やはり原始再帰的関数として構成できる．
]<Computability_BoundedMinificationUpperRemark>

=== $n$番目の素数の計算

素数について成り立つ，次の定理 #ref(<Computability_NextPrimeSearchRange>)を用いることで，$i$番目の素数を出力する関数を原始再帰的関数として構成することが出来る．

#theorem(name: "素数の探索範囲の上界について")[
  $p_n$が$n$番目の素数のとき，次の素数である$n + 1$番目の素数$p_(n+1)$は$p_n ! + 1$以下に存在する．
]<Computability_NextPrimeSearchRange>

#proof[
  TODO:
]

#definition[
  $n$番目の素数を出力する関数を，$fnPrime(n) : Nat2Nat(1)$とする．
  ただし，素数は0番目から数えるとする．すなわち，$fnPrime(0) = 2, fnPrime(1) = 3, ...$である．
]

#theorem[
  関数$fnPrime$は原始再帰的関数である．
]

#proof[
  #ref(<Computability_NextPrimeSearchRange>)より次の素数の探索範囲は$fnPrime(n)! + 1$すなわち有界であるので，有界最小化によって素数を探索することができる．

  したがって，所望の関数$fnPrime$は以下のように定義すればよい．
  $
    fnPrime(0) &:= 2 \
    fnPrime(succ(n)) &:= fnBMinimize(y, fnPrime(n)! + 1, fnPrime(n) < y and RPrime(y))
  $

  これまでに次のことを証明してきた#footnote[もちろん，これより多くのことが後ろで積み上がっている．ここでは代表的なものを取り上げた．]．
  - 階乗が原始再帰的関数として表せること．(#ref(<Computability_PrimRecFn2>))
  - $RPrime$が原始再帰的関係であること．(#ref(<Computability_RPrimeIsPrimRec>))
  - 有界最小化の上界を原始再帰的関数で定義してもよいこと． (#ref(<Computability_BoundedMinificationUpperRemark>))

  これらの結果を踏まえれば，定義した関数が原始再帰的であることは明らか．
]

#example[
  本当になっているか確かめてみよう．

  - $fnPrime(1) = fnBMinimize(y, fnPrime(0)! + 1, fnPrime(0) < y and RPrime(y)) = fnBMinimize(y,
  3, 2 < y and RPrime(y)) = 3$
  - $fnPrime(2) = fnBMinimize(y, fnPrime(1)! + 1, fnPrime(1) < y and RPrime(y)) = fnBMinimize(y, 7, 3 < y and RPrime(y)) = 5$
  - $fnPrime(3) = fnBMinimize(y, fnPrime(2)! + 1, fnPrime(2) < y and RPrime(y)) = fnBMinimize(y, 121, 5 < y and RPrime(y)) = 7$

  $fnPrime(3)$の有界最小化の探索範囲を見ればわかるとおり，この関数の計算効率は非常が悪い#footnote[100番目の素数$523$を求める$fnPrime(100)$で有界最小化の探索範囲はおよそ$10^158$となる．]．
  しかしながら，この計算は必ずいずれ終わるのである．
]

= 1階述語論理

== 構文論

== 小さな構文論

#definition(name: "アルファベット")[
  以下の8個の記号をアルファベットという．
  $ prime space.quad f space.quad P space.quad not space.quad -> space.quad exists space.quad hash space.quad triangle.r.small $
]<FOL_Alphabet>

#definition(name: "略記")[
  - $f, P$を$n >= 1$個並べた記号列$underbrace(f dots.c f, n), underbrace(P dots.c P, n)$を，それぞれ$f_n, P_n$と略記する．
  - $f_n, P_n$の後に$prime$を$m >= 0$個並べた記号列$underbrace(f dots.c f, n) overbrace(prime dots.c prime, m), underbrace(P dots.c P, n) overbrace(prime dots.c prime, m)$を，それぞれ$f_n^m, P_n^m$と略記する．
  - $hash$を$n$個並べた記号列$underbrace(hash dots.c hash, n)$を，$hash_n$と略記する．
]

== 算術の言語

#definition(name: "算術の言語")[
  よって特徴づけられる言語を，算術の言語$ArithmeticLanguage$という．
]<FOL_ArithmeticLanguage>

= Gödelの第1不完全性定理

== 可証性述語

#theorem[
  $
    T proves sigma ==> T proves Provability(TheoryT, GoedelNumTerm(sigma))
  $
]<GoedelIT_Drv1>

== Gödelの不動点補題

#theorem(name: "Gödelの不動点補題")[
  $x$のみを自由変項とする任意の論理式$phi(x)$について，次を満たす文$sigma$を構成することが出来る．

  $
    T proves sigma <-> phi(GoedelNumTerm(sigma))
  $

  このとき，$phi(x)$が$Sigma_n$論理式であるならば，$sigma$は$Sigma_n$文となる．同様に，$phi(x)$が$Pi_n$論理式であるならば，$sigma$は$Pi_n$文となる．
]<GoedelFPLemma>

#definition(name: "Gödel文")[
  $Provability(TheoryT, x)$が可証性述語であるとき，不動点補題 #ref(<GoedelFPLemma>)によって構成される次の文$GoedelSentence$を，理論$TheoryT$のGödel文という．
  $
    TheoryT proves GoedelSentence <-> not Provability(TheoryT, GoedelNumTerm(GoedelSentence))
  $
]<GoedelSentence>

#theorem(name: "Gödelの第1不完全性定理")[
  $TheoryT$を$PeanoArithmetic$の再帰的可算な拡大理論であるとし，$GoedelSentence$を$TheoryT$のGödel文とする．このとき，以下が成り立つ．
  - $TheoryT$が無矛盾ならば，$TheoryT proves.not GoedelSentence$．
  - $TheoryT$が$Sigma_1$健全ならば，$TheoryT proves.not not GoedelSentence$．

  故に，$TheoryT$が無矛盾かつ$Sigma_1$健全ならば，$TheoryT$は不完全である．
]<GoedelIT1>

#proof(name: $T proves.not GoedelSentence$ + "の証明")[
  + $TheoryT proves GoedelSentence$だと仮定する．
  + #ref(<GoedelIT_Drv1>)より$TheoryT proves Provability(TheoryT, GoedelNumTerm(GoedelSentence))$であり，$GoedelSentence$の定義より$TheoryT proves not GoedelSentence$となる．
  + 纏めれば$T proves G$かつ$T proves.not G$であるが，$TheoryT$は無矛盾であると前提しているため，この議論は破綻する．

  よって仮定がおかしく，$TheoryT proves.not GoedelSentence$である．
]

#proof(name: $T proves.not not GoedelSentence$ + "の証明")[
  + $TheoryT proves not GoedelSentence$だと仮定する．
  + $GoedelSentence$の定義より$TheoryT proves Provability(TheoryT, GoedelNumTerm(GoedelSentence))$となる．
  + $Provability(TheoryT, GoedelNumTerm(GoedelSentence))$が$Sigma_1$文であるため，$TheoryT$が$Sigma_1$健全であることから$StandardArithmeticModel models Provability(TheoryT, GoedelNumTerm(GoedelSentence))$となる．
  + $StandardArithmeticModel models Provability(TheoryT, GoedelNumTerm(GoedelSentence))$と$T proves G$は同値である．
  + 纏めれば$T proves not GoedelSentence$かつ$T proves GoedelSentence$であるが，$TheoryT$は$Sigma_1$健全すなわち無矛盾であると前提しているため，この議論は破綻する．

  よって仮定がおかしく，$TheoryT proves.not not GoedelSentence$である．
]

#remark(name: "Gödel文の真偽")[
  Gödel文の定義より，以下が成り立つ．
  $
    StandardArithmeticModel models GoedelSentence iff StandardArithmeticModel models not Provability(TheoryT, GoedelNumTerm(GoedelSentence)) iff T proves.not GoedelSentence
  $

  ここで，#underline[$T$が無矛盾であると仮定するならば] #ref(<GoedelIT1>)より$TheoryT proves.not G$であるので$StandardArithmeticModel models GoedelSentence$である．
  しかしながら，#ref(<GoedelIT1>)はGödel文は証明も反証も出来ないということ，すなわちGödel文の証明可能性についてだけ触れているのであって，Gödel文の真偽については何も触れていないことに注意せよ．

  Gödel文の真偽は$T$が#underline[実際に]無矛盾であるかどうかに依存しており，その事実は第1不完全性定理によって示されたりはしない．
  故に，第1不完全性定理を「正しいが証明は出来ない言明が存在する」と短絡的に帰結することは若干の危険または誤りがある．
]

== Gödel-Rosserの第1不完全性定理

#ref(<GoedelIT1>)において，不完全性を示す#footnote[より細かく言えば$TheoryT proves.not not GoedelSentence$であることを示すことを．]ためには，無矛盾性より強い条件である$Sigma_1$健全性を仮定せざるを得なかった．
この仮定を無矛盾性に弱められることがRosserによって示されている．そのためには，可証性述語を少し変更して，Rosser可証性述語と呼ばれるものに置き換える必要がある．

=== Rosser可証性述語

#definition(name: [Rosser可証性述語])[
]<RosserProvability>

= Gödelの第2不完全性定理

ここでは，$TheoryT$とは算術の理論の拡大とする．

== 導出可能性条件

#definition(name: [Hilbert-Bernays-Löbの導出可能性条件])[
  $sigma,pi$を文とする．
  $TheoryT$の可証性述語$Provability(TheoryT,x)$について，次の条件$Drv1,Drv2,Drv3$を，Hilbert-Bernays-Löbの導出可能性条件と呼ぶ．
  $
    Drv1 &: T proves sigma ==> T proves Provability(TheoryT, GoedelNumTerm(sigma)) \
    Drv2 &: T proves Provability(TheoryT, GoedelNumTerm(sigma -> pi)) -> (Provability(TheoryT, GoedelNumTerm(sigma)) -> Provability(TheoryT, GoedelNumTerm(pi))) \
    Drv3 &: T proves Provability(TheoryT, GoedelNumTerm(sigma)) -> Provability(TheoryT, GoedelNumTerm(Provability(TheoryT, GoedelNumTerm(sigma)))) \
  $
]<DerivabilityCondition>

#definition(name: [標準的可証性述語])[
  $Drv1,Drv2,Drv3$を満たす理論$TheoryT$の可証性述語$Provability(TheoryT, x)$を，標準的可証性述語という．
]

#definition(name: [無矛盾性を表す文])[
  $TheoryT$で反証可能な$Sigma_1$文を1つ取ってきて$bot$とする#footnote[すなわち，$TheoryT proves not bot$である．]．
  $TheoryT$の無矛盾性を表す文$Consistency(TheoryT) := not Provability(TheoryT, GoedelNumTerm(bot))$と定義する．
]<Consistency>

#remark[
  $Consistency(TheoryT)$は$Pi_1$文である．
]

#theorem(name: [形式化された$Sigma_1$完全性定理])[
  任意の$Sigma_1$文$sigma$に対して次が成立する．
  $
    TheoryT proves sigma -> Provability(TheoryT, GoedelNumTerm(sigma))
  $
]<FormalizedSigma1Completeness>

#lemma[
  $Provability(TheoryT, x)$が標準的可証性述語であるとき，
  任意の文$sigma$に対して次が成立する．
  $
    TheoryT proves not Provability(TheoryT, GoedelNumTerm(sigma)) -> Consistency(TheoryT)
  $
]<GoedelIT2_GoedelSentenceConsistencyEquality_lem1>

#let TheoryU = $U$
#lemma[
  任意の$PeanoArithmetic$の拡大理論$TheoryU$と任意の文$sigma$に対して次が成立する．
  $
    U proves Provability(TheoryT, GoedelNumTerm(sigma)) -> Provability(TheoryT, GoedelNumTerm(not sigma)) ==> TheoryU proves Consistency(T) -> not Provability(TheoryT, GoedelNumTerm(sigma))
  $
]<GoedelIT2_GoedelSentenceConsistencyEquality_lem2>

#lemma[
  任意の$TheoryT$のGödel文$GoedelSentence$に対して次が成立する．
  $
    TheoryT proves Consistency(TheoryT) -> not Provability(T, GoedelNumTerm(GoedelSentence))
  $
]<GoedelIT2_GoedelSentenceConsistencyEquality_lem3>

#proof[
  + $not GoedelSentence$は$Sigma_1$文であるので，形式化された$Sigma_1$完全性定理 #ref(<FormalizedSigma1Completeness>)より$TheoryT proves not G -> Provability(TheoryT, GoedelNumTerm(not GoedelSentence))$．
  + $GoedelSentence$の定義より，$TheoryT proves Provability(TheoryT, GoedelNumTerm(GoedelSentence)) -> not G$．
  + 1,2より，$TheoryT proves Provability(TheoryT, GoedelNumTerm(GoedelSentence)) -> Provability(TheoryT, GoedelNumTerm(not GoedelSentence))$．
  + #ref(<GoedelIT2_GoedelSentenceConsistencyEquality_lem2>)と3より，$TheoryT proves Consistency(TheoryT) -> not Provability(TheoryT, GoedelNumTerm(GoedelSentence))$．
  以上で示された．
]

#theorem(name: [Gödel文と無矛盾性の同値性])[
  $TheoryT$のGödel文$GoedelSentence$と，$TheoryT$の無矛盾性を表す文$Consistency(TheoryT)$とが，標準的可証性述語によって構成されているとき，次が成立する．
  $
    TheoryT proves GoedelSentence <-> Consistency(TheoryT)
  $
]<GoedelIT2_GoedelSentenceConsistencyEquality>

#proof[
  + #ref(<GoedelIT2_GoedelSentenceConsistencyEquality_lem1>)に$GoedelSentence$を適用して$TheoryT proves not Provability(TheoryT, GoedelNumTerm(GoedelSentence)) -> Consistency(TheoryT)$．
  + #ref(<GoedelIT2_GoedelSentenceConsistencyEquality_lem3>)と1を合わせて，$TheoryT proves not Provability(TheoryT, GoedelNumTerm(GoedelSentence)) <-> Consistency(TheoryT)$．
  + Gödel文の定義より，$TheoryT proves GoedelSentence <-> Consistency(TheoryT)$．
  以上で示された．
]

#ref(<GoedelIT2_GoedelSentenceConsistencyEquality>)より，明らかに次の系が成り立つ．

#corollary[
  任意の$TheoryT$のGödel文$GoedelSentence,GoedelSentence'$に対して$TheoryT proves GoedelSentence <-> GoedelSentence'$
]

#theorem(name: [Gödelの第2不完全性定理])[
  $TheoryT$が$PeanoArithmetic$の再帰的可算な拡大理論であるとする．このとき，以下が成り立つ．
  - $TheoryT$が無矛盾ならば，$TheoryT proves.not Consistency(TheoryT)$
  - $TheoryT$が$Sigma_1$健全ならば，$TheoryT proves.not not Consistency(TheoryT)$
]<GoedelIT2>

#proof[
  第1不完全性定理(#ref(<GoedelIT1>))とGödel文と無矛盾性の同値性(#ref(<GoedelIT2_GoedelSentenceConsistencyEquality>))より従う．
]

#remark[
  第2不完全性定理#ref(<GoedelIT2>)の対偶も重要な応用がある．すなわち，#underline[自身の無矛盾性が$TheoryT$で証明できてしまう#footnote[$TheoryT proves Consistency(TheoryT)$．]なら，$TheoryT$は矛盾している]という事実はよく用いられる．
]<GoedelIT2_Contradiction>

== Kreiselの注意

#ref(<GoedelIT2>)においてもGödel-Rosserの第1不完全性定理のように$Sigma_1$健全を弱めることが出来ないのだろうか？これは出来ないのである．

#theorem[
  Rosser可証性述語は導出可能性条件$Drv2,Drv3$を同時に満たさない．
]

#corollary(name: [Kreiselの注意])[
  $TheoryT proves not RosserProvability(TheoryT, GoedelNumTerm(bot))$．ただし$bot$は #ref(<Consistency>)での用法と同じ#footnote[すなわち例えば文$0 = 1$などのことを指す．]とする．

  言い換えれば，#ref(<Consistency>)で用いる可証性述語としてRosser可証性述語を利用して無矛盾性を表した文$RosserConsistency(TheoryT) := not RosserProvability(TheoryT, GoedelNumTerm(bot))$を構成した場合は，第2不完全性定理は成り立たない．
]

= Löbの定理

Gödelの不動点補題と可証性述語を組み合わせると，様々な自己言及的な文を構成することが出来る．
Gödel文は自己の証明不可能性を主張する文として定義されたが，逆に，自己の証明可能性を主張する文を考えるとどんなことが起こるのか考えてみよう．

#definition(name: [Henkin文])[
  $Provability(TheoryT, x)$が可証性述語であるとき，不動点補題#ref(<GoedelFPLemma>)によって構成される次の文$HenkinSentence$を，理論$TheoryT$のHenkin文という．
  $
    TheoryT proves HenkinSentence <-> Provability(TheoryT, GoedelNumTerm(HenkinSentence))
  $
]<HenkinSentence>

このとき，#underline[Henkin文は$TheoryT$で証明可能なのか？]という問題がHenkin#cite("henkin_1952")によって提案された．この問題はLöb#cite("loeb_1955")によって，より一般的な形で解決された．

#theorem(name: [Löbの定理])[
  任意の文$sigma$に対して次が成立する．
  $
    TheoryT proves sigma iff TheoryT proves Provability(TheoryT, GoedelNumTerm(sigma)) -> sigma
  $
]

$==>$については自明なので，問題は$<==$を証明することである．この証明には第2不完全性定理を使う証明(#ref(<OriginalLoebTheoremProof>))と，第2不完全性定理を使わないLöbのオリジナルの証明(#ref(<OriginalLoebTheoremProof>))がある．特に後者の証明からは第2不完全性定理が系として得られる(#ref(<LoebTheoremImplyGoedelIT2>))．

前述の通り，Löbの定理はHenkinの問題を一般化したものであり，$sigma$を$HenkinSentence$とすればHenkinの問題は解決される．

#corollary[
  $TheoryT proves HenkinSentence$である．
]

== Löbの定理の意義

== 第2不完全性定理を用いた証明 <LoebTheoremProofByGoedelIT2>

第2不完全性定理は証明済みとする．このときLöbの定理は次のように証明される．

#proof[
  $TheoryT proves Provability(TheoryT, GoedelNumTerm(sigma)) -> sigma$を仮定する．
  対偶と演繹定理より，$TheoryT + not sigma proves not Provability(TheoryT, GoedelNumTerm(sigma))$となる．

  ここで，$Drv2$の対偶として$TheoryT + not sigma proves (Provability(T, GoedelNumTerm(not sigma)) and Consistency(TheoryT)) -> not Provability(TheoryT, GoedelNumTerm(not sigma -> bot))$が成り立つ．$not Provability(TheoryT, GoedelNumTerm(bot)) equiv Consistency(TheoryT)$であることに注意．

  $TheoryT + not sigma proves not sigma$と$Drv1$より$TheoryT proves Provability(T, GoedelNumTerm(not sigma))$であり，
  $TheoryT + not sigma proves not Provability(TheoryT, GoedelNumTerm(sigma))$と#ref(<GoedelIT2_GoedelSentenceConsistencyEquality_lem1>)より$TheoryT + not sigma proves Consistency(TheoryT)$である．
  よって，$TheoryT + not sigma proves not Provability(TheoryT, GoedelNumTerm(not sigma -> bot))$である．

  更に，形式化された演繹定理より，$T + not sigma proves not Provability(TheoryT + not sigma, GoedelNumTerm(bot))$となる．
  ここで，$not Provability(TheoryT + not sigma, GoedelNumTerm(bot)) equiv Consistency(TheoryT + not sigma)$であることに注意すれば，$T + not sigma proves Consistency(TheoryT + not sigma)$である．
  このとき，第2不完全性定理より$TheoryT + not sigma$は矛盾してしまう#footnote[#ref(<GoedelIT2_Contradiction>)も参照せよ．]ことがわかる．よって，$TheoryT proves sigma$である．
]

== オリジナルのLöbの証明 <OriginalLoebTheoremProof>

一方，Löbのオリジナルの証明では第2不完全性定理を用いておらず，不動点補題を用いてKreisel文と呼ばれる文を構成し，それに基づいて証明している．

#let KreiselSentence = $K$
#definition[
  任意の文$sigma$に対して，不動点補題を用いて構成される次の文$KreiselSentence$を，$TheoryT$のKreisel文と呼ぶ．
  $
    TheoryT proves KreiselSentence <-> (Provability(TheoryT, GoedelNumTerm(KreiselSentence)) -> sigma)
  $
]

それでは証明しよう．

#proof[
  $TheoryT proves Provability(TheoryT, GoedelNumTerm(sigma)) -> sigma$を仮定する．

  また，Kriesel文$KreiselSentence$として$TheoryT proves KreiselSentence <-> (Provability(TheoryT, GoedelNumTerm(KreiselSentence)) -> sigma)$を構成する．

  以下の議論によって，$T proves Provability(TheoryT, GoedelNumTerm(KreiselSentence)) -> Provability(TheoryT, GoedelNumTerm(sigma))$が成り立つ．
  + $TheoryT proves Provability(TheoryT, GoedelNumTerm(KreiselSentence)) -> Provability(TheoryT, GoedelNumTerm(Provability(TheoryT, GoedelNumTerm(KreiselSentence)) -> sigma))$．
    - $Drv1$より以下が成り立ち，これを$KreiselSentence$の定義と合わせる．
      - $TheoryT proves KreiselSentence ==> TheoryT proves Provability(TheoryT, GoedelNumTerm(KreiselSentence))$．
      - $TheoryT proves Provability(TheoryT, GoedelNumTerm(KreiselSentence)) ==> TheoryT proves Provability(TheoryT, GoedelNumTerm(Provability(TheoryT, GoedelNumTerm(KreiselSentence))))$．
  + $TheoryT proves Provability(TheoryT, GoedelNumTerm(KreiselSentence)) -> (Provability(TheoryT, GoedelNumTerm(Provability(TheoryT, GoedelNumTerm(KreiselSentence)))) -> Provability(TheoryT,sigma))$．
    - $Drv2$より$TheoryT proves Provability(TheoryT, GoedelNumTerm(Provability(TheoryT, GoedelNumTerm(KreiselSentence)) -> sigma))) -> (Provability(TheoryT, GoedelNumTerm(KreiselSentence)) -> Provability(TheoryT, GoedelNumTerm(sigma)))$であり，これと1を合わせる．
  + $T proves Provability(TheoryT, GoedelNumTerm(KreiselSentence)) -> Provability(TheoryT, GoedelNumTerm(sigma))$．
    - $Drv3$より$TheoryT proves Provability(TheoryT, GoedelNumTerm(KreiselSentence)) -> Provability(TheoryT, GoedelNumTerm(Provability(TheoryT, KreiselSentence)))$であり，これと2を合わせる．

  仮定と合わせて#ref(<OriginalLoebTheoremProof_eq>)が成り立つ．
  #math.equation(block: true, numbering: "(1)")[
    $T proves Provability(TheoryT, GoedelNumTerm(KreiselSentence)) -> sigma$
  ] <OriginalLoebTheoremProof_eq>

  ここで，#ref(<OriginalLoebTheoremProof_eq>)と$KreiselSentence$の定義より$T proves KreiselSentence$であり，$Drv1$より$T proves Provability(TheoryT, GoedelNumTerm(KreiselSentence))$である．
  再び#ref(<OriginalLoebTheoremProof_eq>)を用いれば，$T proves sigma$となる．
]

=== Löbの定理の系としての第2不完全性定理 <LoebTheoremImplyGoedelIT2>

== 形式化されたLöbの定理

Löbの定理は形式化することが可能である．

#theorem(name: [形式化されたLöbの定理])[
  任意の文$sigma$に対して次が成立する．
  $
    TheoryT proves Provability(TheoryT, GoedelNumTerm(Provability(TheoryT, GoedelNumTerm(sigma)) -> sigma)) -> Provability(TheoryT, GoedelNumTerm(sigma))
  $
]

後に$Provability(TheoryT, x)$を単なる様相演算子$square$として見ることになるが，その際に重要な働きとなる．

= Robinson算術についての第2不完全性定理

= 算術$WeakestArithmetic$について

Robinson算術$RobinsonArithmetic$よりも更に弱い算術でも不完全性定理を証明することができる．
そのような算術の例として，Tarski,Mostowski,Robinsonによって算術$WeakestArithmetic$が与えられた#cite("tarski_mstowski_robinson_1953")．
この章では，この$WeakestArithmetic$について見ていこう．#cite("vaught_1966", "jones_shepherdson_1983")に基づく．

= Boolosの不完全性定理

= 様相論理

= 証明可能性論理

= Kolmogorov複雑度

= Chaitinの不完全性定理

= 抜き打ちテストのパラドックスの形式化

驚くべきことに，抜き打ちテストのパラドックスを上手く形式化すると，第2不完全性定理が得られるということが分かっている．
この章では#cite("kritchman_raz_2010")に基づき，その証明を見ていくことにしよう．

= 連結の理論

不完全性はどこからやって来るのか？Quineの考察#cite("quine_1946")によれば，それは算術よりもっと根源的な操作である「連結」という操作からやってくるという．
この章では#cite("grzegorczyk_2005", "grzegorczyk_zdanowski_2007")などで提案された，連結の理論(Concatenation Theory)について見ていくことにしよう．

= 自己検証可能な理論

#bibliography("bib.yml", style: "ieee")
