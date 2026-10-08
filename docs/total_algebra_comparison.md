# 原論文の総代数・Gr(A)との比較

原論文§1.2–§1.4では、成分の有限台直和を代数とし、接続しない成分の積を零とする。
既存定義では `A.Hom i j = e_j A e_i`、`A.comp b a = b*a` である。
`docs/source.pdf`の該当箇所と再照合し、この向きを保持した。

`TotalAlgebraEmbedding.lean`は、`⊕_(i,j) A.Hom i j`を正則右加群の
自己準同型へ線形に写す。直和の包含・射影と線形Yonedaにより成分を回収し、単射性を証明する。
`TotalAlgebra.lean`は、像の積の閉性を証明し、mathlibのNonUnitalSubalgebraとして
総代数を構成する。有限台空間との線形同値はすべての元を対応させるため、任意のPropによる代数の代用ではない。
接続する積は元の合成であり、接続しない積は零である。結合律は実際のEndの積から継承する。

`TotalAlgebraLocalUnits.lean`は、恒等成分の有限和が冪等であり、
任意の有限個の代数元を左右から固定することを、実際の有限台から証明する。
局所単位の存在をAS条件へ追加していない。

`TotalComponentActions.lean`は、既存LeftModule/RightModuleの総空間の成分作用が
加法・スカラー倍・接続する積と非接続積の零性を保つことを証明する。
`TotalAlgebraLift.lean`の延長補題をこの証明済み法則へ適用し、
`TotalModuleRepresentations.lean`で全総代数への左・右作用を構成する。
右作用は反変性により反対Endへ写す。任意の追加仮定に依存したAS双対性ではない。

LocallyUnitalModules.leanで、単位化上のModuleCatのうち、恒等成分の有限和が各元を固定する
実際の部分圏と、左右総加群の対象・所属の証明を構成した。単位化の全ModuleCatをGr(A)と同一視してはいけない。
TotalModuleFunctors.leanで射の対応と左右の忠実関手を構成済み。
TotalModuleFullness.leanで任意の総加群射から自然変換を回収し、左右関手の充満性も証明済み。
残る任意の対象の成分射影像・直接和分解、逆関手、有限台分解の一意性、単位・余単位の自然性と
圏同値を証明し、その同値による実際のAbelian.Extの保存を示す必要がある。
忠実性とexactnessだけからExt保存を結論しない。

原論文(1.12)の成分モデルでのExt直和交換と全成分左作用への適合性は前回証明済み。
今回の総代数構成だけでは、原論文Gr(A)内の(1.12)全体の完成とは扱わない。
有限長双対性・周期性、定理3.2と系5.2の正式なLean定理文と証明は未完成。
