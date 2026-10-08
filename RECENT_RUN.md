# 一般radical・最小分解・Extへの継続記録

実測開始：2026-10-08 11:15:27 JST（2026-10-08T02:15:27+00:00、秒精度）。
目的：最終のAS–Ginzburg対応へ向け、未完了の一般radicalの閉性・minimality・有限分解・Ext接続を進める。
最新の明示的な指示に従い、自律的に継続し、検証した単位を直接mainへpushする。新規PRなし。
開始HEAD d928baf。mainとorigin/main一致、clean。前回最終記録コミットのActions 37716539463はsuccess。
AGENTS/HANDOFF/STATUS/GAPS/最新検証・回収記録と入力PDF §1.2 (1.5)–(1.7)を再読。
右作用はM_v×A_vu→M_u。最小性は各微分の像が対象のM A_{>0}に入ること。
AS条件に周期性やExt同型を追加せず、定理3.2・系5.2を完成扱いにしない。
作業中。完成単位・検査・終了時刻は逐次追記する。

## 単位1：任意のMの正次数radical

positiveActionSpanが右作用と任意の加群の射で保たれることをspanの帰納法で証明。
既存RightSubmoduleを使う実際のradicalと、包含を保つ線形radical endofunctorを構成。
representableでは前回のradicalの成分と等しいことを証明。
次：微分の像がradicalに入るminimality、radicalを経由する因子化、単純商へのHomでの消滅。

検証：`20261008T021911Z-bde25aca`、64.300385秒、全段階終了0。
開始UTC 2026-10-08T02:19:11.659768+00:00、終了UTC 2026-10-08T02:20:15.960160+00:00。
254異なる宣言・112 theorem・39 named instanceを監査。
差分：runs/radical-resolution-20261008-unit1.patch。

## 単位2：実際の像包含としてのminimality

IsMinimalMorphismは各成分の像がpositiveActionSpanに入るという具体的な条件。
線形写像のrangeの包含との同値、radicalへの実際の自然変換による因子化との同値を証明。
零射と左右の合成で最小性が保たれることを証明。
任意Propでの置換ではなく、原論文の微分に対する明示的な像の条件をそのまま実装。
次：単純加群へのHomに適用した微分の消滅、有限四項分解の微分・完全性を束ねる。

検証：`20261008T022127Z-7488f1f7`、65.271972秒、全段階終了0。
開始UTC 2026-10-08T02:21:27.495705+00:00、終了UTC 2026-10-08T02:22:32.767686+00:00。
263異なる宣言・119 theorem・39 named instanceを監査。
差分：runs/radical-resolution-20261008-unit2.patch。

## 単位3：単純加群へのHomと最小微分の消滅

s_iの正次数radicalは零。任意のM→s_iはMのradicalを消すことを証明。
したがって最小微分fにHom(-,s_i)を適用した微分は実際に零。
Extとの比較を仮定した結果ではなく、具体的な自然変換の合成の消滅。
次：四項の実際の有限直和と微分・完全性・最小性を束ね、Hom複体を接続する。

保存経路の変更：単位2のCLI git pushは認証エラーで終了128（2試行）。
接続済みGitHub APIで同一tree 6cc6630be5539026fd2d848566b19dc8c7acab92を作成し、
6068d7e8e87d21464111973a74cf27d7209312cfをmainへ通常のfast-forwardで保存。
expected_shaを照合、force=false、新規PRなし。元のローカルb935aacはcheckpoint/cli-minimality-20261008へ保持。
APIで作られたcommit objectのSHAを再構成して確認し、ローカルmainも6068d7eへ同期。
ファイル内容を変えず、履歴・ログを保持した。以後も認証済みAPIで保存できる。

検証：`20261008T022802Z-48535cdc`、66.187648秒、全段階終了0。
開始UTC 2026-10-08T02:28:02.786776+00:00、終了UTC 2026-10-08T02:29:08.974429+00:00。
266異なる宣言・122 theorem・39 named instanceを監査。
差分：runs/radical-resolution-20261008-unit3.patch。

## 証明単位4：原論文(1.6)の具体的な有限最小分解データ

`ASResolution.lean`でincoming/outgoing arrowsを有限型として定義し、lifted endpointと高さの対応を証明した。
有限直和を実際のrepresentableのcoproductで定義し、射影性を普遍性から証明した。
`ASResolution`は原論文(1.6)の四つの射影項、三つの微分、既存のs_vへの射、
隣接合成の零、三箇所のmathlib `ShortComplex.Exact`、左端Mono、既存radicalへの像の包含を持つ。
このデータからHom(-,s_i)の三つの微分が零であることを証明した。
任意のAについてこの分解が存在するという定理は未証明であり、存在は原論文AS定義(i)の内容である。
次：この具体的データからmathlib ProjectiveResolutionを構成し、実際のExtとの比較を証明する。


検証：`20261008T023459Z-4389600a`、69.911236秒、全段階終了0。
開始UTC 2026-10-08T02:34:59.904668+00:00、終了UTC 2026-10-08T02:36:09.815913+00:00。
285異なる宣言・130 theorem・43 named instanceを監査。
差分：runs/radical-resolution-20261008-unit4.patch。

## 証明単位5：実際の導来圏Extのk線形構造

`RightModuleExtLinear.lean`で標準導来圏のlocalizationからk線形構造を構成した。
既存の`Abelian.Ext`の加法群を保ち、実際のShiftedHomとの同型からModule構造を移した。
0次の`Ext.mk₀`がスカラー倍を保つこと、Homおよびrepresentableの頂点評価との線形同型を証明した。
必要なExt同型を新しい仮定にしていない。高次のHom複体との比較はまだ未証明。
mathlibの古いleftDerived型`Ext`と新しい`Abelian.Ext`は別定義であり、
古い`ProjectiveResolution.isoExt`だけを新しいExtとの比較として扱わない。
次：原論文(1.7)の総次元を実際のExtのModule.rankで定義し、有限分解の比較を進める。
単位4のGitHub main保存：982f6a1a6fef4edce4dbbf490166854c00b46d2a。


検証：`20261008T023950Z-d459766f`、84.797827秒、全段階終了0。
開始UTC 2026-10-08T02:39:50.396901+00:00、終了UTC 2026-10-08T02:41:15.194736+00:00。
295異なる宣言・131 theorem・48 named instanceを監査。
差分：runs/radical-resolution-20261008-unit5.patch。

## 証明単位6：有限最小分解からmathlib ProjectiveResolutionへの変換

`ASResolutionComplex.lean`で四項をdegree≥4で零に延長した実際のChainComplexを構成した。
全項の射影性、正次数のexactness、s_vへのaugmentationのQuasiIsoを証明し、
与えられたASResolutionをmathlib `ProjectiveResolution s_v`へ変換した。
degree n+4のIsZeroも証明済み。ASResolutionの存在は任意のAについて未証明であり、
原論文のAS定義(i)の存在条件として扱う。比較同型やAS双対性は仮定していない。
次：実際のHom複体を構成し、新しいderived-category Extとの比較を証明する。
単位5のmain保存：44667b2b14d7fe895a9fe215873642389e79fbd5。


検証：`20261008T024407Z-dc54759b`、86.544521秒、全段階終了0。
開始UTC 2026-10-08T02:44:07.074024+00:00、終了UTC 2026-10-08T02:45:33.618552+00:00。
305異なる宣言・134 theorem・50 named instanceを監査。
差分：runs/radical-resolution-20261008-unit6.patch。

## 証明単位7：原論文AS定義(i)(ii)の具体化

`ASRegular.lean`で有限最小分解の存在と実際の`Abelian.Ext(s_u,P_v)`の全次数・全被覆頂点の
総Module.rank=1を定義した。第二引数P_vを固定しており、periodicityやdelta型のExt表は仮定していない。
無限次元のfinrankが0になる問題を避け、Cardinal値のrankを使った。
AS条件から各Extのrank≤1、Module.Finite、finrank≤1を証明した。
rank=0と実際のExtの全要素が零である条件の同値、AS分解を選んだ実際のProjectiveResolution、
degree≥4のIsZeroも証明済み。
任意のAやJacobian代数についてAS条件の成立は未証明。
既存presheafモデルと原論文の局所単位元付きGr(A)の明示的同値も未証明である。
次：Hom複体との実際の比較、(3,tau v)の非零Extの特定、命題1.3のdelta形と左加群同型。
単位6のmain保存：4072a79452b2705726ca34dc4cadba10ebe27594。


検証：`20261008T024855Z-af8ca59e`、104.812992秒、全段階終了0。
開始UTC 2026-10-08T02:48:55.882947+00:00、終了UTC 2026-10-08T02:50:40.695946+00:00。
315異なる宣言・140 theorem・50 named instanceを監査。
差分：runs/radical-resolution-20261008-unit7.patch。

## 証明単位8：実際のHom複体と単純加群に対する零微分

`ASResolutionHomComplex.lean`でHom(R_n,N)と実際のprecompositionのk線形写像から
mathlib CochainComplexを構成した。合成の零、全微分のminimality、Hom(-,s_i)の全微分の零を証明した。
そのホモロジーと各次数の実際のHom空間とのModuleCat同型も構成した。
このホモロジーをderived-category Abelian.Extと同定する定理はまだ未証明。
利用先：有限最小分解から単純加群間Extを計算する比較定理、および命題1.3のHom複体。
次：実際のExtのk線形なconnecting mapとdimension shifting、AS分解のsyzygyとの接続。
単位7のmain保存：285ab93e129538ce06d1c86dc7c0c1581f588ce2。


検証：`20261008T025237Z-333fbf43`、107.744968秒、全段階終了0。
開始UTC 2026-10-08T02:52:37.301336+00:00、終了UTC 2026-10-08T02:54:25.046310+00:00。
323異なる宣言・145 theorem・50 named instanceを監査。
差分：runs/radical-resolution-20261008-unit8.patch。

## 証明単位9：命題1.3の実際のHom項

`ASDualityHomTerms.lean`でincoming sourceの高さがvより大きいことをwinding<periodから証明した。
s_(tau v)の分解の最初の三つの射影項からP_vへのHomが零であることを、
representableHom_vanishesと有限coproductの普遍性から証明した。
最左項のHom(P_v,P_v)とkの線形同型も既存のconnected条件から構成した。
利用先：命題1.3のHom複体0→0→0→kの実際の計算。
残る義務：そのホモロジーと実際のExtの比較、delta型Ext表・左加群作用・周期性。
単位8のmain保存：62d49b86e80d5e7b5c61c23fcb2ff97ecb9f1497。


検証：`20261008T025544Z-34a6fcc8`、110.826843秒、全段階終了0。
開始UTC 2026-10-08T02:55:44.372772+00:00、終了UTC 2026-10-08T02:57:35.199626+00:00。
328異なる宣言・149 theorem・50 named instanceを監査。
差分：runs/radical-resolution-20261008-unit9.patch。

## 証明単位10：実際のExtの線形connecting mapと次元シフト

`RightModuleExtSequence.lean`で標準導来圏のshiftのk線形性とExtのYoneda積の双線形性を証明した。
mathlibの短完全列のextClassから実際のExtのk線形なconnecting mapを構成した。
中間項が射影的なら正次数のconnecting mapは全単射で、実際のExtの線形なdimension shiftになる。
0次の場合はHom(S.X₂,N)=0の証明も必要で、これを明示して線形同型を証明した。
このHom消滅は原論文命題1.3の高い頂点の射影項にはASDualityHomTermsから導けるが、
AS有限分解をsyzygyの短完全列に切り分けてこの同型を合成する接続はまだ未証明。
比較同型を仮定に追加していない。任意のPropや独自axiomによる代替もない。
次：ASResolutionのkernel/imageのsyzygy短完全列を構成し、実際のExt³(s_(tau v),P_v)をkと同定する。
単位9のmain保存：d2b1091edb908b5df735254639ded644d56b4994。


検証：`20261008T025935Z-9dac7919`、118.847390秒、全段階終了0。
開始UTC 2026-10-08T02:59:35.218932+00:00、終了UTC 2026-10-08T03:01:34.066331+00:00。
336異なる宣言・153 theorem・51 named instanceを監査。
差分：runs/radical-resolution-20261008-unit10.patch。

## 証明単位11：命題1.3の実際のHom cohomology

`ASDualityHomCohomology.lean`でs_(tau v)の有限分解にHom(-,P_v)を適用した
実際の複体の0,1,2次の項と4次以降の項がIsZeroであることを証明した。
3次ホモロジーとkの線形同型、finrank=1、他の全次数のホモロジーのIsZeroも証明した。
この時点ではderived-category Abelian.Extとの比較は未証明。
次：syzygy短完全列から線形dimension shiftを合成して実際のExt³を計算する。
単位10のmain保存：719f8521a6909533a39c57f8d6573b55a84c5b97。


検証：`20261008T030308Z-ec72e438`、121.208460秒、全段階終了0。
開始UTC 2026-10-08T03:03:08.873014+00:00、終了UTC 2026-10-08T03:05:10.081482+00:00。
342異なる宣言・158 theorem・51 named instanceを監査。
差分：runs/radical-resolution-20261008-unit11.patch。

## 証明単位12：具体的なsyzygy短完全列

`ASResolutionSyzygies.lean`で最小分解のd₁をkernel(s_vへの射)へ、d₂をそのcoverのkernelへ
持ち上げる実際のmodule mapを構成した。元のexactnessから両coverのEpiと持ち上げ後のexactnessを証明した。
これにより三つのmathlib ShortComplex.ShortExactを構成した。
利用先：単位10の線形dimension shiftの三段合成によりExt³(s_(tau v),P_v)を計算する。
ASResolutionの存在以外の新しいAS仮定は追加していない。
単位11のmain保存：28fb8bbc90f35385301a06ec7588a69dfa291ef6。


検証：`20261008T030649Z-8b35b460`、126.194093秒、全段階終了0。
開始UTC 2026-10-08T03:06:49.133793+00:00、終了UTC 2026-10-08T03:08:55.327889+00:00。
356異なる宣言・168 theorem・53 named instanceを監査。
差分：runs/radical-resolution-20261008-unit12.patch。

## 証明単位13：実際のExt³(s_(tau v),P_v)=k

`ASDualityExt.lean`で三つのsyzygy短完全列の線形connecting isomorphismを合成した。
最初の0次shiftに必要なHom消滅は単位9の高い頂点の射影項の計算から導いた。
既存のExt⁰–Hom線形同型とHom(P_v,P_v)=kを使い、実際のderived-category
Abelian.Ext³(s_(tau v),P_v)とkの線形同型を構成した。ASRegularから選んだ分解でも使える。
そのfinrank=1とrank=1を証明した。必要なExt同型を仮定に追加していない。
命題1.3の一つの非零位置が実際のExtとして完成。全Extのdelta型と左加群AS双対性はこの単位では未証明。
次：総Cardinal rank=1から他のExtを零とし、原論文(1.11)の数値的な順方向を証明する。
単位12のmain保存：cd1a2a5a0dfcc696a362fd9aaf7a38b9396f9e37。


検証：`20261008T030958Z-4779ab4b`、134.503781秒、全段階終了0。
開始UTC 2026-10-08T03:09:58.505756+00:00、終了UTC 2026-10-08T03:12:13.009546+00:00。
360異なる宣言・170 theorem・53 named instanceを監査。
差分：runs/radical-resolution-20261008-unit13.patch。

## 証明単位14：実際のExtのdelta型次元公式と有限台

`ASDualityDimension.lean`でCardinal.sum=1の他の非零項が存在しないことをsigma型のSubsingletonから証明した。
実際のExt³のrank=1と原論文(1.7)の総rank=1から、(3,tau v)以外の全Abelian.Extが零であることを証明した。
ASRegular.ext_finrankは原論文(1.11)の数値的な順方向で、実際のExtに対するdelta型の公式である。
その有限台を証明し、関数が実際のExtのfinrankであるFinsupp表を構成、既存の数値単位へ接続した。
Hom cohomologyとExt³の二つのkとの証明済み線形同型を合成したdegree-three比較も構成した。
一般のM,Nと全次数の自然なHom複体–Ext比較とは別である。
ここでは左加群AS双対性(1.12)、同値の逆方向、AS条件からの周期性、Gr(A)との明示的同値は未証明。
定理3.2・系5.2も未証明で、形式的な文も未実装。
次：有限生成分解のA-dual・左作用・直和との交換から(1.12)、有限長双対性と区間同型を導く。
単位13のmain保存：cb51f14ee4f68785d58f1b9846c6688706e8535e。


検証：`20261008T031342Z-13ba299c`、161.737727秒、全段階終了0。
開始UTC 2026-10-08T03:13:42.658554+00:00、終了UTC 2026-10-08T03:16:24.396290+00:00。
369異なる宣言・177 theorem・53 named instanceを監査。
差分：runs/radical-resolution-20261008-unit14.patch。
