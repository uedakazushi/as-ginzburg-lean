# 現在の状況

有限台成分空間を忠実な正則表現の像と線形同一視し、積の閉性から実際の非単位的総代数を構成しました。
元のA.Hom成分の接続する積と、接続しない積の零性を証明済み。原論文の積の向きと全既存仮定を保持しています。
次は両側局所単位、その後、総加群作用・成分逆関手・Gr(A)圏同値と実際のExt保存です。
有限長双対性・周期性・主定理3.2と系5.2は未証明。両主結果の形式的な文も未実装です。
最新ローカル検証 20261008T071757Z-d3bbdf9d：62数学モジュール・657異なる宣言・283 theorem、全段階終了0。
単位1〜2の差分・実測時刻・次の義務はRECENT_RUN.mdとruns/total-algebra-20261008.md。

2026年10月8日。定理3.2・系5.2は**未証明、形式的な定理文も未実装**です。

既存の線形RightModuleを保ち、有限AS分解だけから全次数のExt(s_w,P_i)の有限性と次数4以上の消滅を証明しました。
有限AS分解の存在の下で、元のASRegularと式(1.11)の数値条件の両方向の同値が証明済みです。
具体的な左加群・A-dual・左単純商を構成し、実際のExt(s_w,P_i,p)の成分左加群が
p≠3で零、p=3でs^left_(tau^{-1}w)に同型であることを左作用ごと証明しました。
Hom(P_i,-)・Ext⁰(P_i,-)の余極限交換、左側の射影性・EnoughProjectives・実際のExtの存在も完成しました。
左A-dualも構成し、左右のrepresentableが二重A-dualで元に戻る同型を証明しました。
既存モデルのExt(s_w,⊕P_i)への直和交換は完成。原論文のGr(A)比較、周期性と主定理は未証明です。

開始時の51数学モジュールに今回9モジュールを追加。8証明単位を個別Leanと全体ビルド・公理監査で検査してmainへ保存。
初期14モジュール・入力PDF・checkpoints/・recovery/は無変更。

| 項目 | 現在の結論 |
|---|---|
| lake build | 成功、終了0 |
| 個別公理監査 | 657異なる名前、全明示的宣言・116 named instanceを含む、終了0 |
| theorem | 283、全件が監査対象 |
| sorry / admit / 独自axiom | ソース0件 |
| 許容公理 | propext、Classical.choice、Quot.soundのみ |
| 禁止依存 | sorryAx、Lean.ofReduceBool、Lean.trustCompilerなし |
| 主結果 | 定理3.2・系5.2は未証明、文も未実装 |
| 保存 | 直接main、GitHub APIで通常のfast-forward、新規PRなし |

最新ローカル検証 `20261008T062041Z-c4ef97ab`：全段階終了0、320.816787115秒。
JST 2026-10-08T15:20:41.062310+09:00 → 2026-10-08T15:26:01.879105+09:00。
UTC 2026-10-08T06:20:41.062310+00:00 → 2026-10-08T06:26:01.879105+00:00。
11回帰テスト、ソース監査、固定環境、lake build、全宣言の#print axioms、照合が成功。

## 形式化状況

| 論文中の位置 | Leanファイル | 実装・証明済み | 残る範囲 |
|---|---|---|---|
| §1.1、(1.1) | `CutQuiver.lean` | cut箙、被覆頂点、heightの全単射、正のwinding、pathの次数公式 | 被覆道代数をZ-代数として束ねる同定 |
| §1.1の巡回空間 | `CutPotential.lean` | 回転商の自由ベクトル空間、cut次数、唯一のcutの分割とnormal form | 閉じた可合成道の部分空間とkQ/[kQ,kQ]の同定 |
| (3.8) | `CyclicDerivative.lean` | 巡回微分の実装、回転不変性、cut復元恒等式 | Jacobianイデアルおよび商代数との接続 |
| 道代数 | `PathAlgebra.lean` | 成分の自由ベクトル空間、双線形積、単位元、結合則 | 関係イデアルとその商、unrolling |
| (1.4) | `ZAlgebra.lean` | 具体的な成分、双線形な積、局所単位元、connected・positive・finite条件 | 原論文のモデルとの明示的同値・AS条件の成立 |
| 命題1.2の帰納法 | `ZAlgebra.lean` | 成分が生成元と短い積に分解されれば全成分を生成する | 分解条件を最小射影分解から導くこと、核が矢イデアルの二乗に入ること |
| (1.5) | `Representables.lean` | k線形圏と右線形presheaf、YonedaのHom同型、逆向きHomの消滅、自己Homの次元1 | 直和・局所単位元付き加群との明示的同値 |
| §1.2の加群圏・(1.6)の基盤 | `RightModuleAbelian.lean`、`RightModuleHomology.lean` | (余)極限の閉性、Abelian構造、核・余核・homologyの成分同型、exactness・短完全列・mono/epiの成分判定 | 一般の自然なHom複体–Ext比較 |
| (1.5)の射影対象 | `RightModuleProjectives.lean`、`RightModuleEnoughProjectives.lean` | 全Mへの線形Yoneda同型、P_vの射影性、representableの直和による射影提示、EnoughProjectives | 有限生成のprojective coverと最小分解 |
| (1.5)の単純商 | `RightSubmodules.lean`、`SimpleRightModules.lean` | 右作用で閉じた部分加群、商の短完全列、P_v A_{>0}との成分同定、s_vの対角1次元・他の成分零とSimple | 原論文Gr(A)との明示的同値 |
| (1.6)–(1.7)の基盤 | `RightModuleExt.lean` | 標準projective resolutionと正次数exactness、実際のderived-category Ext、Ext⁰(P_i,M)≃+M_i、高次Ext(P_i,M)=0 | 全M,N・全次数の自然なHom複体–Ext比較 |
| 命題1.3の数値段階 | `ExtDimension.lean` | 有限台の自然数次元表の総和1と非零項1からdelta形を導く | 原論文のExt(s_w,A)版の左加群双対性とGr(A)比較（数値的両方向は完成） |
| 命題1.3のtop Hom計算 | `TopCohomology.lean` | 前の空間が零ならtop cokernelはそのまま、値域kなら次元1 | 一般の自然な比較（今回、命題1.3の3次は接続済み） |
| 命題1.4の貼り合わせ | `WindowPeriodicity.lean` | coherentな区間同型から積と単位元を保つ周期同型を構成 | D Ext³から区間同型を作る部分全体 |
| 命題3.1の共役段階 | `Conjugation.lean` | 完全忠実な線形関手と対象同型から、積を保つHom線形同型を構成 | tilting、Serre functor、高次preprojectiveとの同定 |
| §4、§5の数値計算 | `Hilbert.lean` | 一般の正のlagの漸化式の一意性、quadratic Hilbert値、増大上界 | exact resolutionからのEuler式、del Pezzo模型との幾何的比較 |
| 系5.2の線形表示 | `Tensor333.lean` | 実際の三重テンソル積、係数表示、cut関係への同型、27次元、基底変更 | tensor・potential・Jacobian代数の完全な比較 |
| 系5.2の箙 | `Triangle333.lean` | 三角形箙、全矢のwinding=1、cut次数1閉路の長さ3、明示的potentialのcut恒等式 | 箙自己同型とGL(X)×GL(Y)×GL(Z)の群・商の同定 |
| (1.3)の次数 | `GinzburgGrading.lean` | a、a*、t_vの型と三つの次数、windingの正値性、loop項の次数 | dg代数、d²=0、コホモロジー、Ginzburg正則性 |
| 一般radical・minimality | RightModuleRadical、RightModuleMinimality、RightModuleSimpleHom | 閉性・自然性、radicalを通る因子化、Hom(-,s_i)の零微分 | 有限生成projective coverの一般理論 |
| (1.6)の具体的分解 | ASResolution、ASResolutionComplex、ASResolutionSyzygies | 有限coproductの射影性、完全最小列、mathlib ProjectiveResolution、三つの実際の短完全列 | 特定の代数について分解の存在 |
| (1.7)の具体的条件 | RightModuleExtLinear、ASRegular | 実際Extのk作用、Ext⁰の線形同型、総Cardinal rank=1、各Extの有限次元性 | Gr(A)への明示的同値・Ext保存 |
| 命題1.3の順方向 | ASResolutionHomComplex、ASDualityHomTerms、ASDualityHomCohomology、RightModuleExtSequence、ASDualityExt、ASDualityDimension | 実際のHom複体、線形dimension shift、実際Ext³≃k、他Ext消滅、(1.11)の数値公式と有限台 | Gr(A)比較による原論文(1.12)、周期性、一般の自然なHom–Ext比較 |
| 有限AS分解からのExt有限性・数値的同値 | ASResolutionExtBounds、RightModuleHomFinite、ASResolutionExtFinite、ASDualityEquivalence | 任意Nへの次数4以上の消滅、Ext(s_w,P_i,p)の全次数有限性、(1.7)と(1.11)の両方向 | 原論文Gr(A)との比較 |
| 左加群・左単純商・Ext左作用 | LeftModules、LeftModuleAbelian、LeftModuleHomology、LeftSubmodules、SimpleLeftModules、RightModuleExtLeftAction、ASDualityLeftComponents | 左Abelian圏、A-dual、左radical商、Simple、Ext成分左加群の次数集中と左単純商への同型 | 成分作用を総代数の作用に束ね、Gr(A)との圏同値・Ext保存 |
| 余極限交換と左射影基盤 | RepresentableHomColimits、LeftModuleProjectives、LeftModuleEnoughProjectives、LeftModuleExt | Hom(P_i,-)・Ext⁰(P_i,-)の自然な交換、左線形Yoneda・射影性・EnoughProjectives・標準分解・実際Ext | 一般の二重双対・有限生成射影への拡張、Gr(A)比較 |
| 左A-dualとrepresentableの二重双対 | LeftModuleADual | 左A-dualの実際の右作用、左右のrepresentableの二重A-dualが元に同型 | 一般の評価写像の自然性、有限生成射影・perfect complexへの拡張 |
| 有限Homと自然なExt長完全列 | FiniteCoproductHomColimits、RightModuleExtNaturalSequence | 有限Homの交換、Extの接続写像・次元シフトの自然性と余核表示 | 一般の自然なHom複体–Ext比較 |
| exactな余極限と核・余核の交換 | HomologicalColimitClosure、RightModuleHomKernel | 核・余核の交換の閉性、小さい直和のexactness、Homの自然な核表示 | 特定の代数で有限AS分解の存在 |
| 全次数Extと直和の交換 | ASResolutionExtColimits | 有限AS分解だけからExt(s_w,-,n)のexactな余極限・小さい直和保存、包含射への適合性 | Gr(A)との圏同値による移送 |
| 総空間・直和上の実際の左作用 | ASDualityRegularCoproduct、TotalModuleSpaces、RegularCoproductActions | Ext(s_w,⊕P_i,n)の成分総空間比較、ASから次数3集中、左右総空間関手の忠実性とexactness、実際の行列作用・積・局所単位・Ext交換の成分左作用適合性 | 有限台非単位的総代数と局所単位付き加群、逆関手・圏同値・Ext保存 |
| 総空間の有限局所単位 | TotalModuleLocalUnits | 具体的有限射影の冪等性、左右の恒等成分作用との一致、任意の有限個の元の同時固定、右成分作用の包含への適合性 | 総代数・加群構造を束ね、成分逆関手・Gr(A)圏同値・Ext保存 |

## 主結果の状態

| 主張 | 状態 |
|---|---|
| 定理3.2：一般の型QのAS–Ginzburg対応 | 未証明。形式的な定理文も未実装 |
| 命題1.3 | 既存モデルの数値的両方向とExt成分の左単純商への同型は証明済み。全次数の直和交換と成分作用適合性は証明済み。総代数・Gr(A)比較・Ext保存は未証明 |
| 命題1.4：AS条件からの周期性 | 未証明。coherentな区間同型を仮定した最後の貼り合わせのみ |
| 命題5.1：三周期性 | 未証明 |
| 系5.2：(3,3,3)型の全単射 | 未証明。形式的な定理文も未実装 |

## 条件付き結果と残る義務

ASResolutionの存在は原論文定義(i)の条件をモデル化したもの。任意のAで導いたとは扱わない。
ASRegularの条件には周期性・WindowSystem・delta型のExt表・主定理相当の結論を含めない。
既存の数値表・共役・WindowSystemの補題の入力を原論文から導く未証明部分も残る。
標準無限分解だけから有限性を主張しない。
古いleftDerived型ExtのisoExtを新しいAbelian.Extの比較定理と取り違えない。

- 原論文の局所単位元付き直和加群Gr(A)と既存presheafモデルの明示的同値、Ext保存。
- 全M,N・全次数の自然なHom複体–Abelian.Ext比較。命題1.3の3次比較は証明済み。
- A-dual・左単純商の同型、全次数Extと直和の交換、成分左作用への適合性は完成。総非単位的代数・局所単位付き加群を束ね、Gr(A)圏同値とExt保存を証明する部分が残る。原論文(1.12)全体は未完成。
- 有限長双対性、区間同型のcoherence、AS条件からの周期性。WindowSystemをAS条件に加えない。
- 特定のJacobian代数についてAS分解の存在、Jacobian商とGinzburg dg代数、外部一般定理、主定理の同型類対応。

ソースにsorry/admit/独自axiomなし。公理依存はpropext、Classical.choice、Quot.soundのみ。
sorryAx、Lean.ofReduceBool、Lean.trustCompilerへの依存なし。
新規数学ファイルに未解決のコンパイルエラー・lint警告なし。既存のlint警告は残存。
161は初期成果の件数で、宣言数の固定条件ではありません。

今回の証明単位はruns/ext-sums-20261008-unit*.patchと新規verification/runs/に保存。
前回のruns/radical-resolution-20261008-unit*.patchも保持。
今回の実測時刻・終了コード・次の義務・main保存先はruns/ext-sums-20261008.mdとRECENT_RUN.md。
初期14数学モジュール・入力PDFの旧SHA-256一致、recovery/とcheckpoints/の無変更を再確認。
今回の保存確認はverification/ext_sums_preservation.json。ルートimportと生成AxiomAuditは意図した更新。
CLI git pushの認証エラー(終了128)後、接続済みGitHub APIへ切り替えた。
ローカル検証済みtreeのSHA一致とexpected_shaを確認し、force=falseでmainを通常のfast-forward保存。
ローカルmainも同じAPI commit objectに同期。CLIの認証が修復されたという主張はしない。
新規PRなし。mainへのpush・最新Actionsとartifactの確認はRECENT_RUN.md参照。

ユーザーは形式化の自律的継続を明示的に指示。通常の補題について再開確認は不要。

以前のradical-resolutionタスクの最終数学コミットc314180のmain CI 37722129359はsuccess、12ファイルの当該実行artifact保存済み。
CI実行の時刻と終了0はverification/radical_resolution_github_ci_evidence.json・CI logに保存。

現在の優先課題は総非単位的代数・総加群構造の構成、Gr(A)との圏同値とExt保存。
今回8単位の対応・仮定・利用先はdocs/ext_coproduct_exchange.md。
差分・検査・実測時刻・main保存先はRECENT_RUN.mdとruns/ext-sums-20261008.md。
初期14モジュール、開始時51モジュール、PDFと歴史的な487ファイルの保存確認はverification/ext_sums_preservation.json。
前回の数値的同値・左双対の証拠はverification/as_finiteness_github_ci_evidence.jsonと同名のCI logに保持。
今回の正確な数学headのCI・artifact成功を確認済み。RECENT_RUN.mdとverification/ext_sums_github_ci_evidence.json参照。

最終数学コミット6666e09の[main CI](https://github.com/uedakazushi/as-ginzburg-lean/actions/runs/37737755500)はsuccess。
636異なる宣言・全274 theoremの新規監査、全7段階終了0、12ファイルのartifact 11532667814保存を確認。
CI検証UTC 2026-10-08T06:28:37.911543+00:00 → 2026-10-08T06:36:04.010329+00:00、単調時計446.098779473秒、終了0。
証拠はverification/ext_sums_github_ci_evidence.jsonと同名のCI log。
この確認後の終了記録の保存は文書・ログのみ。同じ数学ソースを保持し、そのpushも新規CIを開始する。
