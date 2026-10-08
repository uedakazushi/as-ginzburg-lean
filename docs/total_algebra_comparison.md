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
UnitizationComponentActions.leanで、任意の単位化上の左右加群の成分作用と、恒等成分の直交冪等な射影を証明済み。
UnitizationComponentModules.leanで射影像の成分加群を構成し、元の作用・恒等射・合成・加法・k線形性を証明済み。
UnitizationComponentFunctors.leanで成分射と自然変換の復元関手を構成済み。
UnitizationComponentSums.leanで成分直和の和の写像・単射性と、局所単位条件からの全射性・k線形直和同型を証明済み。
LocallyUnitalEquivalence.leanで和の写像の全単位化作用への適合性・加群同型・自然性、
具体的成分逆関手と単位・余単位による左右圏同値を完成した。
LocallyUnitalAbelian.leanで左右関手のk線形性と、局所単位付き圏のAbelian構造・EnoughProjectives・実際のHasExtを証明済み。
ExactEquivalenceExt.leanで一般の導来圏の同値・single complex・shiftへの適合性とExt同型を構成し、
LocallyUnitalExtComparison.leanで全M,N・全次数の左右Extのk線形同型を証明した。
LocallyUnitalExtNaturality.leanで全次数Ext比較の前合成・後合成の自然性も証明した。
正則総加群と総代数の同定と(1.12)への移送も完成した（末尾の各単位を参照）。
忠実性とexactnessだけからExt保存を結論しない。

原論文(1.12)の成分モデルでのExt直和交換と全成分左作用への適合性は前回証明済み。
圏同値、全次数のk線形Ext同型と自然性、正則総加群の同定、全左乗法作用への適合性、具体的Gr(A)内の(1.12)の左加群同型を完成した。
有限長双対性・周期性、定理3.2と系5.2の正式なLean定理文と証明は未完成。

RegularTotalAlgebra.leanで正則右総空間の有限台二重直和・総代数とのk線形同型、成分包含と行列元の対応、成分および全総代数の右作用と右乗法の一致を証明した。実際の局所単位付き右加群対象・加群同型・左乗法の同定が次の義務。

RegularRightModule.leanで総代数の実際の単位化右加群、スカラー作用と右乗法の作用式、局所単位付き対象、正則総加群との加群同型、成分左乗法の右加群射と具体式を構成・証明した。全左乗法とExtの移送が次の義務。

LinearExtTransport.lean、RegularLeftMultiplication.lean、RegularExtComparison.leanにより、実際のExt(Fs_w,A)と元のExt成分左加群の総空間をk線形に比較した。自然なExt保存・正則右加群の同型・有限AS分解の直和交換を合成し、任意の総代数元の左乗法による後合成と全左表現の一致を証明した。左Ext加群としての束ねと次数3の単純商同型を次に公開検証する。

RegularExtLeftModule.leanで実際のExt(Fs_w,A)の単位化左作用を構成し、その作用式を元のk作用と実際の左乗法による後合成で証明した。局所単位付き左加群と元のExt成分左加群の総加群との同型を構成し、ASRegularから次数3の左単純商同型と他の全次数の零性を証明した。式(1.12)の順方向をこの具体的モデルで完成した。有限長双対性・周期性・主定理は引き続き未完成。
