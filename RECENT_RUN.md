# AS有限分解・次元条件の継続形式化

目的：有限AS分解だけから実際のExtの消滅・有限性を導き、命題1.3の数値条件の逆方向へ接続する。
既存RightModule・実際のAbelian.Extを保ち、追加の周期性やExt同型を仮定しない。
定理3.2・系5.2は未証明、形式的な定理文も未実装。

実測開始UTC：2026-10-08T03:32:03+00:00（秒精度のclock観測）。
開始main：a3debe134d372c9b2d47d9fd601a5ea64a332993。
開始時点の同コミットActions 37722967530：success。
AGENTS/HANDOFF/STATUS/GAPS・現行/回収results・最新runを読み、原論文§1.2–1.3を照合済み。
終了記録時の実測UTC：2026-10-08T04:40:14+00:00。開始から4091秒（秒精度UTC観測値の差）。
範囲は9単位の実装・検査・数学コミット保存・そのCI確認・文書整備まで。最終記録コミットの保存と後続CIは範囲外。

保存は接続済みGitHub APIで直接main、通常のfast-forward、force=false、新規PRなし。
CLI git pushの前回認証不具合を修復したという主張はしない。

## 単位1：有限AS分解から全ターゲットへの次数4以上のExt消滅

三つの実際のsyzygy短完全列を通る線形dimension shiftを構成した。
最左のrepresentableの射影性から、任意NへのExt(s_w,N,n+4)は全要素零、rank=0。
ASResolutionの存在は原論文(i)の条件であり、総rank=1の(ii)は使っていない。
利用先：有限AS分解からのExt有限性、逆向きの次元条件、有限長双対性。
次：有限coproductのHomとkernelのHomの有限性、低次Extの長完全列による有限性。

初回全体run 20261008T033924Z-3e8fa100はルートimportの配置ミスでbuild終了1。
importを冒頭へ移し、下記の新規runで全段階終了0を確認した。失敗ログも保持。

検証：`20261008T034026Z-887b3beb`、155.891924秒、全段階終了0。
UTC 2026-10-08T03:40:26.273705+00:00 → 2026-10-08T03:43:02.165634+00:00。
372異なる宣言・179 theorem・53 named instance。
差分：runs/as-finiteness-20261008-unit1.patch。

単位1のmain保存：7117937fdc3351dbc2cb4a7caa8cd5e2bbbe0b5b。tree一致を確認してAPIでfast-forward。

## 単位2：有限AS分解からExt(s_w,P_i)の全次数の有限性

有限coproductのHom–Pi線形同型、epiによるHomへの線形単射、線形YonedaからHomの有限性を証明した。
実際のExtの長完全列でExt¹をkernelのHomの商として扱い、次数2・3はsyzygyのdimension shiftで移した。
次数4以上は単位1の消滅を使い、全Ext(s_w,P_i,p)のModule.Finiteを得た。
ASResolutionの存在とZAlgebraの局所有限性だけを使い、総rank=1やdelta表を仮定していない。
利用先：finrank表からCardinal rank条件への逆方向、有限生成分解の双対性。
次：実際のfinrankのdelta条件と元のASRegularとの同値を証明する。

検証：`20261008T034423Z-c7c903db`、167.034188秒、全段階終了0。
UTC 2026-10-08T03:44:23.495487+00:00 → 2026-10-08T03:47:10.529682+00:00。
384異なる宣言・189 theorem・53 named instance。
差分：runs/as-finiteness-20261008-unit2.patch。

単位2のmain保存：b8e21f0ffb13da7373384234c7fe9280785e0d3d。

## 単位3：命題1.3の数値条件の両方向

有限AS分解の存在（原論文定義(i)）の下でASRegularと実際のExtのdelta型finrank条件(1.11)の同値を証明した。
逆方向では単位2で得たModule.Finiteを使ってfinrankをCardinal rankへ移し、二重のCardinal.sumが1と証明する。
ASRegularの定義にdelta条件を追加していない。元の定義(ii)との同値を定理として証明した。
原論文Gr(A)との比較、左加群(1.12)、周期性、主定理はまだ未証明。
次：A-dualの実際の左作用、左表現可能加群との同型、Extの左作用の接続。

検証：`20261008T034836Z-7169530c`、167.695902秒、全段階終了0。
UTC 2026-10-08T03:48:36.666276+00:00 → 2026-10-08T03:51:24.362182+00:00。
387異なる宣言・192 theorem・53 named instance。
差分：runs/as-finiteness-20261008-unit3.patch。

単位3のmain保存：e1c6a0210efd18c4ee24674e340338af6bc53046。

## 単位4：具体的な左加群・A-dual・実際Extの左作用

LeftModuleを同じA.Obj上の共変・加法的・k線形なModuleCat値functorとして定義した。
A-dualの成分は実際のHom(M,P_i)、左作用はrepresentableの射への後合成。
P_iのA-dualと左表現可能加群A e_iの左作用を保つ同型を構成した。
実際のAbelian.Extの第2引数におけるk線形functorとExt(s_u,P_i,p)の左作用を構成した。
次数0でこのExt左加群とA-dualが自然に同型であることも証明した。
任意Propによる置換なし。直和へのExtとの比較は未証明で、Ext(M,A)と既に同定したとは扱わない。
次：左加群の核・商と左単純加群、AS条件からのExt左加群の同型。

検証：`20261008T035241Z-63feafce`、181.934901秒、全段階終了0。
UTC 2026-10-08T03:52:41.184345+00:00 → 2026-10-08T03:55:43.119256+00:00。
408異なる宣言・194 theorem・59 named instance。
差分：runs/as-finiteness-20261008-unit4.patch。

単位4のmain保存：e533764c887cfe32366fae3e1b3f7e47f904ccc7。中断後、リモートHEADを再照合して保存。

## 単位5：左加群のAbelian構造と原論文の左単純商

共変な線形左加群の極限・余極限の閉性、Abelian構造、成分ごとのkernel/cokernel/homologyを証明した。
mono/epi、exactness、短完全列を成分で判定できる。
左作用で閉じた具体的LeftSubmoduleと実際の余核商を構成した。
A e_iの正次数部分をpositiveLeftActionSpanと同定し、商simpleLeftModuleをA e_i/A_{>0}e_iとして構成した。
対角成分の次元1、他の成分零、Simple、商の短完全列を証明した。
利用先：(1.12)の左加群双対性と左射影分解、二重双対性。
次：実際Extの左加群をこの商に同定する。直和へのExtの交換はまだ別の義務。

検証：`20261008T035908Z-6c5b631c`、214.299365秒、全段階終了0。
UTC 2026-10-08T03:59:08.990186+00:00 → 2026-10-08T04:02:43.289558+00:00。
464異なる宣言・213 theorem・80 named instance。
差分：runs/as-finiteness-20261008-unit5.patch。

単位5のmain保存：de586c2f70b42e0da84b83050c10a133936e1d7d。
次の単位ではLeftSubmodulesのコメントのcontravariantをcovariantへ修正する（数学的定義は共変で正しかった）。

## 単位6：実際Extの成分左加群と左単純商の同型

ASRegularからExt(s_w,P_i,p)の左加群はp≠3でIsZeroであることを証明した。
次数3では唯一の頂点tau^{-1}wに台をもち、その対角成分の線形同型を左作用を保つ同型へ延長した。
従ってExt成分左加群は実際のsimpleLeftModule(height(tau^{-1}w))に同型で、正次数の左作用は零。
対角作用がスカラーであることはZAlgebra.connectedから証明し、必要な同型を仮定していない。
利用先：原論文(1.12)の左加群構造と有限長双対性。
残る義務：Ext(-,⊕P_i)と⊕Ext(-,P_i)の交換、原論文Gr(A)との明示的同値。
この二つを省いて原論文のExt(s_w,A)版(1.12)が完成したとは扱わない。
次：有限生成射影のHomと直和の交換、比較の自然性と高次Extへの移送。

検証：`20261008T040440Z-db90cc85`、210.410472秒、全段階終了0。
UTC 2026-10-08T04:04:40.274552+00:00 → 2026-10-08T04:08:10.685032+00:00。
470異なる宣言・217 theorem・80 named instance。
差分：runs/as-finiteness-20261008-unit6.patch。

単位6のmain保存：07baa67c2478c4ce6f2cd97fbfe5caf60f3f50fc。

## 単位7：表現可能加群のHomとExt⁰の余極限交換

全右加群に自然な線形YonedaからHom(P_i,-)と頂点評価の自然同型を構成した。
頂点評価は許された全余極限shapeを保存するので、Hom(P_i,-)とその余極限の交換同型を構成した。
実際のExt⁰(M,-)とHom(M,-)の第2引数全体での自然同型を証明した。
これからExt⁰(P_i,-)の余極限保存とcanonicalな交換同型も得た。
利用先：有限生成射影分解のHomと⊕P_iの交換、原論文(1.12)への移送。
次：有限coproductの射影項のHom交換、全次数の自然なHom複体–Ext比較と高次Extの直和交換。
今回の証明だけからExt(s_w,⊕P_i)の交換が完成したとは扱わない。

検証：`20261008T040926Z-5ba129e1`、210.833083秒、全段階終了0。
UTC 2026-10-08T04:09:26.226821+00:00 → 2026-10-08T04:12:57.059910+00:00。
477異なる宣言・217 theorem・83 named instance。
差分：runs/as-finiteness-20261008-unit7.patch。

単位7のmain保存：e2851ad80912db09c81e09dbf4de9d2db39887a7。

## 単位8：左側の線形Yoneda・射影性・EnoughProjectives・実際Ext

全LeftModuleへの線形Yonedaと、A e_iの射影性を共変な左作用から証明した。
全頂点成分の全要素で添字付けたrepresentableのcoproductから任意左加群へのepiを構成した。
この実際の射影提示からEnoughProjectives、標準ProjectiveResolution、実際のAbelian.Extの存在を得た。
左representableのExt⁰は成分評価に加法的に同型で、第一引数にある左representableの高次Extは零。
AS条件の仮定なし。標準分解は無限であり得るので有限AS分解の存在を証明したとは扱わない。
利用先：左側の導来ホモロジー代数、有限生成射影の二重双対、有限長双対性。
次：有限生成射影の双対と二重双対の自然性、右側の高次Extの直和交換、有限長双対性。

検証：`20261008T041353Z-d80bc08c`、225.955783秒、全段階終了0。
UTC 2026-10-08T04:13:53.678555+00:00 → 2026-10-08T04:17:39.634349+00:00。
494異なる宣言・222 theorem・88 named instance。
差分：runs/as-finiteness-20261008-unit8.patch。

単位8のmain保存：ce2fbe48751251b0d8c4b30fa24b363d92e84154。

## 単位9：左A-dualと右・左representableの二重双対

左加群NのA-dualをHom(N,A e_i)の実際の右加群として構成し、反変な射の作用も定義した。
共変な線形Yonedaにより、左representable A e_iのA-dualはP_iと右作用を保って同型。
右・左双方のrepresentableは、この二つの実際のA-dualを重ねると元に同型であると証明した。
AS条件・周期性・Ext同型の仮定なし。標準公理だけの定義と証明。
利用先：有限生成射影とperfect complexの双対性、有限長双対性からの周期性。
残る義務：任意加群へのcanonicalなbidual評価と自然性、有限生成射影の直和・直和因子への拡張、perfect complexでの比較。
一般の二重双対同値や原論文(1.12)の完成とは扱わない。
次：この自然性と有限coproductのHom交換、高次Extの直和交換。

初回全体run 20261008T042349Z-64f44e21はscalar mapのsimp未解決でbuild終了1。
個別処理の完了前に成功と述べた点を訂正し、明示的Linear.smul_compへ修正した。下記の新規runで全段階終了0を確認し、失敗ログも保持。

検証：`20261008T042452Z-24160755`、219.485639秒、全段階終了0。
UTC 2026-10-08T04:24:52.677086+00:00 → 2026-10-08T04:28:32.162732+00:00。
505異なる宣言・223 theorem・91 named instance。
差分：runs/as-finiteness-20261008-unit9.patch。

単位9のmain保存：2863bba9507cd638c09d4d885347abdb42d821fa。

## 最終検査・CI・引継ぎ

9証明単位をそれぞれ新規の全体検査と差分で保存し、直接mainへ通常のfast-forwardで公開した。
開始時35→51数学モジュール、369→505異なる宣言、177→223 theorem、53→91 named instance。
16モジュール・136宣言・46 theorem・38 named instanceを追加。ASRegularの数学的定義は無変更。
最新ローカル検証20261008T042452Z-24160755は219.485638902秒。
11回帰テスト、ソース監査、固定環境、lake build、全宣言#print axioms、照合はすべて終了0。
全223 theoremを含み、重複・漏れ・sorry/admit/独自axiom・禁止依存は零。標準公理はpropext/Classical.choice/Quot.soundのみ。
9回の成功検査の各開始終了・単調時計の実測秒・現在のソースSHA一致はverification/as_finiteness_final_state.json。
初期14モジュール・PDFと19個の歴史的回収/checkpointファイルは無変更、保存確認終了0。git diff --checkも終了0。

今回の最終数学コミット2863bbaの[main CI](https://github.com/uedakazushi/as-ginzburg-lean/actions/runs/37727782672)はsuccess。
505宣言・全223 theoremの新規監査、12ファイルの今回のartifact保存を確認。
CI検証はUTC 2026-10-08T04:30:31.595999+00:00 → 2026-10-08T04:38:32.459227+00:00、
単調時計で480.863225234秒、終了0。
証拠はverification/as_finiteness_github_ci_evidence.jsonと同名のCI log。
この確認後の最終保存は文書・記録のみ。同じ数学ソースを保ち、そのpushでもCIを新規実行する。

初回の単位1・9のbuild終了1は修正済み。両失敗runも削除しない。
未解決のコンパイル・公理監査エラーなし。既存PathAlgebraのunusedSimpArgs警告は残存。
Actionsでは固定checkout/upload-artifactのNode.js 20をrunnerのNode.js 24で実行する非致命的な警告も残存。
前回からのCLI認証エラーは修復していないが、接続済みAPIで検証済みtreeをSHA照合し、expected_sha/force=falseで保存できた。
新規PRなし。HANDOFF/STATUS/GAPS/README/AGENTSとdocs/as_finiteness_left_duality.mdを現状に更新。

次：有限coproductの射影項のHomと直和の交換、高次Extの自然な交換、Gr(A)との明示的同値とExt保存。
一般のbidual評価の自然性、有限生成射影/perfect complexへの拡張、有限長双対性、AS条件からの周期性は未証明。
Jacobian商・Ginzburg dg代数の本体と外部一般定理も必要。定理3.2・系5.2は未証明で、形式的な定理文も未実装。
Ext成分の左単純商への同型を原論文Ext(s_w,A)版(1.12)全体の完成とは扱わない。

実測開始UTC：2026-10-08T03:32:03+00:00。終了記録UTC：2026-10-08T04:40:14+00:00。経過4091秒。
秒精度UTC観測時刻の差であり、各check.shの単調時計実測と区別する。最終記録のAPI保存と後続CIはこの測定範囲外。
詳細はverification/as_finiteness_task_timing.json。未測定の過去の稼働時間を推測していない。
