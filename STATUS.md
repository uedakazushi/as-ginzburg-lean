# 現在の状況

単位114〜131で、canonical A-dual D₁のactual矢公式、original/dualの反対生成元添字と全終点反射、全4項Hom空間と反対射影評価成分の同型を完成。actual native D₁/D₂/D₃の全Jacobian行列反転・Hessian転置と任意元の行列公式、canonical A-dual D₂と反対native D₂の可換性、両端同型の座標と反転D₃有限和公式まで全体ビルド・全宣言公理監査で検証した。
WORK132〜142は個別Lean終了0・診断なし。全3本のcanonical A-dual/native反対微分の可換性と実際のHom短複体の同型・exactness、既存AS項への移送、mathlibの実際Ext⁰/Ext¹/Ext²の全representable標的での零性、Ext³非対角零性、全次数delta型finrankと総Cardinal rank=1を証明。本来のGinzburgRegularから元のASRegular(i)/(ii)全体を導く定理が個別検証済み。これらは今回の548モジュールの全体監査にはまだ含まれない。
WORK143〜159は個別Lean終了0・診断なし。任意のincoming基底の実際の持上げ・全射道表示・核の矢イデアル平方への包含・商同型、最小表示の商同型と商生成性から代数全体の可逆性、評価の自然性を証明。任意の基底変更を実際の自由道ZAlgebra自己同型に持ち上げ、表示との可換性と核のcomap等式まで完成。原論文(3.4)の実際の有限foundation代数と有限次元性を構成し、第零sheetのAS生成元添字＝非cut矢の同値と実際の商基底も証明。これらも公開全体監査には未収録。
未証明：unrolled自己同型の有限cut箙への周期整合した降下、foundationへのexact加群制限・最小関係、AS→Potentialの回収、Keller/Hanihara/Reyesへの接続、Potentialの選択独立性・同型類対応・§5quadratic。定理3.2と系5.2は未証明で、正式Lean定理文も未実装。周期性・必要Ext表・Calabi–Yau性・主結論を新しい仮定にしていない。
最新ローカル検証 20261009T050135Z-ab4e2d31：548数学モジュール・3423異なる宣言・1837 theorem、全段階終了0。
単位1〜131の差分・実測時刻・次の義務はRECENT_RUN.mdとruns/total-algebra-20261008.md。

単位92〜113で、native D₂のactual Hessian行列とnative D₃のactual original矢行列、全有限representable coproductのYoneda座標とcanonical A-dualのtranspose公式を完成。native D₁をactual filtered inclusionのhomologyMapと照合し、mathlib cycle classと実際の境界商classの一致、全filtered代表元のJacobian商公式、original単一矢の恒等元基底とD₁のYoneda行列まで全体ビルド・全宣言公理監査で検証した。
本来のGinzburgRegularから既存最小ASResolution(i)とExt³(s_(τv),P_v)≃ₗk/全次数有限性/AS総rank≥1は完成。native反対GinzburgRegularとの同値、全左単純のfinite genuine ProjectiveResolutionと任意標的へのExt≥4零性、actual path Hessianの反転も全体検証済み。総rank=1/他の低次数・非対角Ext零性/ASRegular(ii)は未証明。行列公式や左単純分解の存在をAS(ii)完成とは扱わない。AS→Φ/最小関係/選択独立性/標準RHom/外部結果/§5quadratic/同型類対応も未証明。定理3.2と系5.2は未証明で、正式Lean定理文も未実装。周期性・必要Ext表・Calabi–Yau性・ASRegularを新たな仮定にしていない。
最新ローカル検証 20261009T041520Z-ba229aab：530数学モジュール・3354異なる宣言・1786 theorem、全段階終了0。
単位1〜113の差分・実測時刻・次の義務はRECENT_RUN.mdとruns/total-algebra-20261008.md。

2026年10月8日。定理3.2・系5.2は**未証明、形式的な定理文も未実装**です。

既存の線形RightModuleを保ち、有限AS分解だけから全次数のExt(s_w,P_i)の有限性と次数4以上の消滅を証明しました。
有限AS分解の存在の下で、元のASRegularと式(1.11)の数値条件の両方向の同値が証明済みです。
具体的な左加群・A-dual・左単純商を構成し、実際のExt(s_w,P_i,p)の成分左加群が
p≠3で零、p=3でs^left_(tau^{-1}w)に同型であることを左作用ごと証明しました。
Hom(P_i,-)・Ext⁰(P_i,-)の余極限交換、左側の射影性・EnoughProjectives・実際のExtの存在も完成しました。
左A-dualも構成し、左右のrepresentableが二重A-dualで元に戻る同型を証明しました。
既存モデルのExt(s_w,⊕P_i)への直和交換は完成。原論文の局所単位付きGr(A)モデルとの圏同値は完成。実際のExtのk線形同型は完成。前合成・後合成の自然性は完成。(1.12)の左加群としての移送も完成。有限次元加群の実際Ext³反変同値と成分線形双対の反変同値は完成。AS条件からの正負周期性は証明済み。主定理は未証明です。

前回ext-sumsでは開始時51数学モジュールに9モジュールを追加。8証明単位を個別Leanと全体ビルド・公理監査で検査してmainへ保存。
初期14モジュール・入力PDF・checkpoints/・recovery/は無変更。

| 項目 | 現在の結論 |
|---|---|
| lake build | 成功、終了0 |
| 個別公理監査 | 3423異なる名前、全明示的宣言・321 named instanceを含む、終了0 |
| theorem | 1837、全件が監査対象 |
| sorry / admit / 独自axiom | ソース0件 |
| 許容公理 | propext、Classical.choice、Quot.soundのみ |
| 禁止依存 | sorryAx、Lean.ofReduceBool、Lean.trustCompilerなし |
| 主結果 | 定理3.2・系5.2は未証明、文も未実装 |
| 保存 | 直接main、GitHub APIで通常のfast-forward、新規PRなし |

最新ローカル検証 `20261009T050135Z-ab4e2d31`、全段階終了0、2268.472920865秒。
UTC 2026-10-09T05:01:35.056814+00:00 → 2026-10-09T05:39:23.529740+00:00。
JST 2026-10-09T14:01:35.056814+09:00 → 2026-10-09T14:39:23.529740+09:00。
11回帰テスト、ソース監査、固定環境、lake build、全宣言の#print axioms、照合が成功。





























































## 現行のGinzburgからASへの証明状態（単位114〜131）

単位114〜131で、canonical A-dual D₁のactual矢公式、original/dualの反対生成元添字と全終点反射、全4項Hom空間と反対射影評価成分の同型を完成。actual native D₁/D₂/D₃の全Jacobian行列反転・Hessian転置と任意元の行列公式、canonical A-dual D₂と反対native D₂の可換性、両端同型の座標と反転D₃有限和公式まで全体ビルド・全宣言公理監査で検証した。

WORK132〜142は個別Lean終了0・診断なし。全3本のcanonical A-dual/native反対微分の可換性と実際のHom短複体の同型・exactness、既存AS項への移送、mathlibの実際Ext⁰/Ext¹/Ext²の全representable標的での零性、Ext³非対角零性、全次数delta型finrankと総Cardinal rank=1を証明。本来のGinzburgRegularから元のASRegular(i)/(ii)全体を導く定理が個別検証済み。これらは今回の548モジュールの全体監査にはまだ含まれない。

WORK143〜159は個別Lean終了0・診断なし。任意のincoming基底の実際の持上げ・全射道表示・核の矢イデアル平方への包含・商同型、最小表示の商同型と商生成性から代数全体の可逆性、評価の自然性を証明。任意の基底変更を実際の自由道ZAlgebra自己同型に持ち上げ、表示との可換性と核のcomap等式まで完成。原論文(3.4)の実際の有限foundation代数と有限次元性を構成し、第零sheetのAS生成元添字＝非cut矢の同値と実際の商基底も証明。これらも公開全体監査には未収録。

未証明：unrolled自己同型の有限cut箙への周期整合した降下、foundationへのexact加群制限・最小関係、AS→Potentialの回収、Keller/Hanihara/Reyesへの接続、Potentialの選択独立性・同型類対応・§5quadratic。定理3.2と系5.2は未証明で、正式Lean定理文も未実装。周期性・必要Ext表・Calabi–Yau性・主結論を新しい仮定にしていない。

過去の単位説明はその時点の状態。完成判定にはこの段落と現行SHAに対応する検査終了コードを使う。


## 形式化状況

| 論文中の位置 | Leanファイル | 実装・証明済み | 残る範囲 |
|---|---|---|---|
| §1.1、(1.1) | `CutQuiver.lean` | cut箙、被覆頂点、heightの全単射、正のwinding、pathの次数公式 | 被覆道代数をZ-代数として束ねる同定 |
| §1.1の巡回空間 | `CutPotential.lean` | 回転商の自由ベクトル空間、cut次数、唯一のcutの分割とnormal form | 閉じた可合成道の部分空間とkQ/[kQ,kQ]の同定 |
| (3.8) | `CyclicDerivative.lean` | 巡回微分の実装、回転不変性、cut復元恒等式 | Jacobianイデアルおよび商代数との接続 |
| 道代数 | `PathAlgebra.lean` | 成分の自由ベクトル空間、双線形積、単位元、結合則 | 関係イデアルとその商、unrolling |
| (1.4) | `ZAlgebra.lean` | 具体的な成分、双線形な積、局所単位元、connected・positive・finite条件 | 総代数モデルは後続単位で構成済み。特定の代数のAS条件の成立 |
| 命題1.2の道代数全射と最小生成元 | ASGenerators、ASPathPresentation、ASMinimalGenerators、ASIndecomposables、CoproductRadicals、CoproductRadicalQuotients、ASGeneratorDimensions、ASGeneratorBasis、UnrolledPathAlgebra、UnrolledPathFiniteness、UnrolledPathZAlgebra、UnrolledPathPresentationMorphism、UnrolledSingleArrows | 最小d₁からの実際のincoming係数、全体生成、自由道ZAlgebra・積/単位元保存と全射、(1.8)の次元式と基底、(1.10)の成分分解 | 核の矢イデアル平方への包含は単位41で完成。任意の基底の持上げ・最小関係・選択の独立性 |
| (1.5) | `Representables.lean` | k線形圏と右線形presheaf、YonedaのHom同型、逆向きHomの消滅、自己Homの次元1 | 局所単位付きGr(A)モデルとの圏同値は後続単位で完成。実際のExtの自然な移送 |
| §1.2の加群圏・(1.6)の基盤 | `RightModuleAbelian.lean`、`RightModuleHomology.lean` | (余)極限の閉性、Abelian構造、核・余核・homologyの成分同型、exactness・短完全列・mono/epiの成分判定 | 一般の自然なHom複体–Ext比較 |
| (1.5)の射影対象 | `RightModuleProjectives.lean`、`RightModuleEnoughProjectives.lean` | 全Mへの線形Yoneda同型、P_vの射影性、representableの直和による射影提示、EnoughProjectives | 有限生成のprojective coverと最小分解 |
| (1.5)の単純商 | `RightSubmodules.lean`、`SimpleRightModules.lean` | 右作用で閉じた部分加群、商の短完全列、P_v A_{>0}との成分同定、s_vの対角1次元・他の成分零とSimple | 単純商のGr(A)モデルへの移送と双対性の比較 |
| (1.6)–(1.7)の基盤 | `RightModuleExt.lean` | 標準projective resolutionと正次数exactness、実際のderived-category Ext、Ext⁰(P_i,M)≃+M_i、高次Ext(P_i,M)=0 | 全M,N・全次数の自然なHom複体–Ext比較 |
| 命題1.3の数値段階 | `ExtDimension.lean` | 有限台の自然数次元表の総和1と非零項1からdelta形を導く | 実際のExt移送による原論文(1.12)の左作用を含む比較 |
| 命題1.3のtop Hom計算 | `TopCohomology.lean` | 前の空間が零ならtop cokernelはそのまま、値域kなら次元1 | 一般の自然な比較（今回、命題1.3の3次は接続済み） |
| 有限区間の代数回収と商射 | TruncatedRepresentableHom、TruncatedRepresentableRestrictions、TruncatedCoverComponents | 元の全代数成分とHomの線形同型、単位元/積保存、下端変更の全射と被覆・Homへの自然性、対角被覆同型と後合成単射性 | 区間商射適合性・coherence・AS周期性は単位38で完成 |
| 有限区間の射影被覆と移送 | NakayamaInverseWindowSupport、NakayamaWindowEquivalence、TruncatedRepresentables、NormalizedProjectiveCovers、FiniteWindowProjectives、NakayamaWindowProjectives | 逆関手の台保存、線形exactな区間同値、実際の切詰めrepresentableの有限性・Yoneda・射影被覆の本質性、End=kと正規化した移送同型 | 代数成分回収・区間coherence・AS周期性も完成 |
| 有限区間と単純の移送 | RightSingleSupportIsomorphism、SimpleVectorDuality、FiniteDimensionalSimpleTranslation、FiniteDimensionalWindows、FiniteDimensionalWindowSequences、NakayamaWindowSupport | 双対の頂点単純同型、ASからNakayamaのτ⁻¹移送、有限区間Abelian構造と包含のexactness、組成列による区間台の負方向シフト | 区間同値・射影被覆・coherenceとAS周期性も完成 |
| 命題1.4のAS周期性 | WindowPeriodicity、NakayamaWindowNormalization、NakayamaWindowComponents、NakayamaWindowCoherence、PeriodInverse、ASPeriodicity | AS条件からの被覆正規化・商射適合性・成分移送のcoherence・正負の周期同型 | 標準RHom/derived/perfectは別の未完成事項 |
| 命題3.1の共役段階 | `Conjugation.lean` | 完全忠実な線形関手と対象同型から、積を保つHom線形同型を構成 | tilting、Serre functor、高次preprojectiveとの同定 |
| §4、§5の数値計算 | `Hilbert.lean` | 一般の正のlagの漸化式の一意性、quadratic Hilbert値、増大上界 | exact resolutionからのEuler式、del Pezzo模型との幾何的比較 |
| 系5.2の線形表示 | `Tensor333.lean` | 実際の三重テンソル積、係数表示、cut関係への同型、27次元、基底変更 | tensor・potential・Jacobian代数の完全な比較 |
| 系5.2の箙 | `Triangle333.lean` | 三角形箙、全矢のwinding=1、cut次数1閉路の長さ3、明示的potentialのcut恒等式 | 箙自己同型とGL(X)×GL(Y)×GL(Z)の群・商の同定 |
| (1.3)の実際の拡張道と微分 | GinzburgGrading、GinzburgPaths、GinzburgPathAlgebra、GinzburgPathWords、GinzburgDegreeZeroAlgebra、GinzburgGeneratorDifferentials、GinzburgGeneratorGradings、GinzburgPathDifferential、GinzburgSupportedProducts、GinzburgDifferentialGradings、GinzburgLeibniz、GinzburgDifferentialSign、GinzburgDegreeZeroDifferential、GinzburgSquareProducts | 実際の道の三次数と道代数、次数0部分との同型、原論文符号の生成元微分・signed線形延長とLeibniz則・次数/cut/winding保存、符号作用素とd²導分則、元/逆矢のsquare-zero | 全square-zero・実際のmathlib複体/homology・GinzburgRegular定義とH⁰の線形比較は単位44で公開検証。積保存・cut/unrolling比較・AS条件との対応は未証明 |
| 一般radical・minimality | RightModuleRadical、RightModuleMinimality、RightModuleSimpleHom | 閉性・自然性、radicalを通る因子化、Hom(-,s_i)の零微分 | 有限生成projective coverの一般理論 |
| (1.6)の具体的分解 | ASResolution、ASResolutionComplex、ASResolutionSyzygies | 有限coproductの射影性、完全最小列、mathlib ProjectiveResolution、三つの実際の短完全列 | 特定の代数について分解の存在 |
| (1.7)の具体的条件 | RightModuleExtLinear、ASRegular | 実際Extのk作用、Ext⁰の線形同型、総Cardinal rank=1、各Extの有限次元性 | 実際のExtのk線形な保存と原論文Gr(A)内のAS条件の比較 |
| 命題1.3の順方向 | ASResolutionHomComplex、ASDualityHomTerms、ASDualityHomCohomology、RightModuleExtSequence、ASDualityExt、ASDualityDimension | 実際のHom複体、線形dimension shift、実際Ext³≃k、他Ext消滅、(1.11)の数値公式と有限台 | (1.12)の移送とAS周期性は完成。一般の自然なHom–Ext比較 |
| 有限AS分解からのExt有限性・数値的同値 | ASResolutionExtBounds、RightModuleHomFinite、ASResolutionExtFinite、ASDualityEquivalence | 任意Nへの次数4以上の消滅、Ext(s_w,P_i,p)の全次数有限性、(1.7)と(1.11)の両方向 | 実際のExt保存によるGr(A)への移送 |
| 左加群・左単純商・Ext左作用 | LeftModules、LeftModuleAbelian、LeftModuleHomology、LeftSubmodules、SimpleLeftModules、RightModuleExtLeftAction、ASDualityLeftComponents | 左Abelian圏、A-dual、左radical商、Simple、Ext成分左加群の次数集中と左単純商への同型 | 総作用と圏同値は完成。実際のExt保存・自然性と原論文(1.12)への移送 |
| 余極限交換と左射影基盤 | RepresentableHomColimits、LeftModuleProjectives、LeftModuleEnoughProjectives、LeftModuleExt | Hom(P_i,-)・Ext⁰(P_i,-)の自然な交換、左線形Yoneda・射影性・EnoughProjectives・標準分解・実際Ext | 一般の二重双対・有限生成射影への拡張、Gr(A)比較 |
| 左A-dualとrepresentableの二重双対 | LeftModuleADual | 左A-dualの実際の右作用、左右のrepresentableの二重A-dualが元に同型 | 一般の評価写像の自然性、有限生成射影・perfect complexへの拡張 |
| 有限Homと自然なExt長完全列 | FiniteCoproductHomColimits、RightModuleExtNaturalSequence | 有限Homの交換、Extの接続写像・次元シフトの自然性と余核表示 | 一般の自然なHom複体–Ext比較 |
| exactな余極限と核・余核の交換 | HomologicalColimitClosure、RightModuleHomKernel | 核・余核の交換の閉性、小さい直和のexactness、Homの自然な核表示 | 特定の代数で有限AS分解の存在 |
| 全次数Extと直和の交換 | ASResolutionExtColimits | 有限AS分解だけからExt(s_w,-,n)のexactな余極限・小さい直和保存、包含射への適合性 | Gr(A)との圏同値による移送 |
| 総空間・直和上の実際の左作用 | ASDualityRegularCoproduct、TotalModuleSpaces、RegularCoproductActions | Ext(s_w,⊕P_i,n)の成分総空間比較、ASから次数3集中、左右総空間関手の忠実性とexactness、実際の行列作用・積・局所単位・Ext交換の成分左作用適合性 | 総代数と左右圏同値は完成。実際のExt保存・自然性と原論文(1.12)への移送 |
| 総代数と左右総作用 | TotalAlgebraEmbedding、TotalAlgebra、TotalAlgebraLocalUnits、TotalComponentActions、TotalAlgebraLift、TotalModuleRepresentations | 有限台の忠実正則表現、像の積の閉性、成分積と零積、冪等な共通両側局所単位、左右総空間への非単位的代数準同型 | 左右圏同値・Abelian構造は後続単位で完成。実際のExt保存・前合成・後合成の自然性も後続単位で完成。(1.12)の移送 |
| 局所単位付き総加群 | LocallyUnitalModules | Unitization上のModuleCat対象、右には反対環、成分作用との一致、局所単位の具体的全部分圏と総加群の所属 | 左右圏同値・Abelian構造は後続単位で完成。実際のExt保存・前合成・後合成の自然性も後続単位で完成。(1.12)の移送 |
| 左右総加群関手 | TotalModuleFunctors | 自然変換の総空間写像、成分・全総代数作用との可換性、単位化上の射、関手の忠実性 | 充満性・左右圏同値は後続単位で完成。実際のExt保存・前合成・後合成の自然性も後続単位で完成。(1.12)の移送 |
| 総加群関手の充満性 | TotalModuleFullness | 誘導k作用の一致、任意の総加群射から成分射と自然変換を回収、元の射の復元、左右のFull instance | 左右圏同値は後続単位で完成。実際のExt保存・前合成・後合成の自然性も後続単位で完成。(1.12)の移送 |
| 任意の単位化加群の成分作用 | UnitizationComponentActions | 元のHom成分の作用、接続積と零積、恒等成分射影の冪等性・直交性 | 成分復元・左右圏同値は後続単位で完成。実際のExt保存・前合成・後合成の自然性も後続単位で完成。(1.12)の移送 |
| 射影像の成分加群 | UnitizationComponentModules | 成分射影像、元のHom作用による閉性、成分写像の恒等射・合成・加法・k線形性、既存LeftModule/RightModule対象の復元 | 成分復元関手・左右圏同値は後続単位で完成。実際のExt保存・前合成・後合成の自然性も後続単位で完成。(1.12)の移送 |
| 成分復元関手と直和分解 | UnitizationComponentFunctors、UnitizationComponentSums | 射の制限と自然変換、左右成分関手、和の写像・成分回収・単射性、局所単位条件からの全射性・k線形同型 | 単位化作用への適合性・自然性・左右圏同値は後続単位で完成。実際のExt保存・前合成・後合成の自然性も後続単位で完成。(1.12)の移送 |
| Gr(A)の局所単位付きモデルとの圏同値 | LocallyUnitalEquivalence | 全総代数作用との可換性、単位化上の和の加群同型・自然性、具体的成分逆関手・単位・余単位・左右圏同値 | Abelian構造は後続単位で完成。実際のExt保存・前合成・後合成の自然性も後続単位で完成。(1.12)の移送 |
| 局所単位付き加群圏のホモロジー基盤 | LocallyUnitalAbelian | 左右関手の加法性・k線形性、圏同値による有限積・Abelian構造・EnoughProjectives・実際のHasExt | 実際のExtのk線形保存と自然性は後続単位で完成。原論文(1.12)への移送 |
| 圏同値による実際のExt保存 | ExactEquivalenceExt、LocallyUnitalExtComparison | 複体・導来圏の同値、single complex・shiftとの適合性、全M,N・全次数の加法的・k線形な実際のExt同型 | 前合成・後合成の自然性と正則総空間の線形同定は後続単位で完成。加群同型・左乗法・原論文(1.12)への移送 |
| 正則右総空間と総代数 | RegularTotalAlgebra | 成分包含と行列元の対応、有限台二重直和とのk線形同型、成分右作用と全総代数右表現の右乗法との一致 | 単位化上の加群同型・局所単位付き右対象と成分左乗法は後続単位で完成。全左乗法と(1.12)への移送 |
| 総代数の局所単位付き正則右加群 | RegularRightModule | 単位化の右作用の具体式、局所単位付き対象、正則総加群との加群同型、左成分乗法の右加群射とその具体式 | 全左乗法と実際のExtへの(1.12)の移送 |
| 総代数への実際Extの移送 | LinearExtTransport、RegularLeftMultiplication、RegularExtComparison | 同型に沿う線形Ext後合成と共役の適合性、全左乗法の右加群射、有限AS分解からGr(A)のExtへの直和比較と全総代数の左作用への適合性 | 局所単位付き左Ext加群、(1.12)の次数3の左単純商同型と他次数零性 |
| 総空間の有限局所単位 | TotalModuleLocalUnits | 具体的有限射影の冪等性、左右の恒等成分作用との一致、任意の有限個の元の同時固定、右成分作用の包含への適合性 | 総代数と左右圏同値は後続単位で完成。実際のExt保存・前合成・後合成の自然性も後続単位で完成。(1.12)の移送 |

| 有限生成射影分解の貼り合わせ | FiniteProjectivePresentations、FiniteProjectiveExtensionClosure、ShortExactKernels、ProjectiveExtensionCovers、FiniteProjectiveResolutionLength、ASFiniteDimensionalResolutionLength | 有限生成射影表示・有限直和と拡大の閉性・snake lemmaによる核の短完全列・実際epiと核を3段繰り返す有限射影分解存在 | 四項複体は後続単位で完成。一般有限次元Mの総正則Ext比較・二重Ext自然同型 |

| 有限次元加群の四項複体とExt交換 | FourTermProjectiveResolution、FiniteProjectiveFourTermResolution、ASFiniteDimensionalProjectiveResolution、ProjectiveResolutionHomExactness、FiniteProjectiveHomColimits、FiniteProjectiveResolutionExtColimits | 全項有限生成射影の実際の四項ProjectiveResolution・次数4以上零性・Hom複体のexactness・右有限次元加群の全次数Extの余極限/直和交換 | 総正則Extへの左作用適合比較・二重Ext自然同型 |

| 総正則Extと二重Ext対象同型 | RightResolutionDuality、LeftResolutionDuality、RightResolutionExtBidual、LeftResolutionExtBidual、FiniteDimensionalExtBidual、FiniteDimensionalRegularExtComparison | 一般四項分解の双対分解・canonical二重Ext対象同型、右有限次元加群の総正則Ext比較と全左作用適合性 | 二重Ext自然同型と有限次元Ext³反変同値は後続単位で完成。左右総正則Ext比較と周期性は完成。標準RHomへの接続 |

| 二重Ext自然同型と有限次元Ext³反変同値 | ExtClassNaturality、ProjectiveResolutionSyzygyNaturality、ResolutionExtBoundaryNaturality、DualResolutionComparisonMaps、ResolutionExtBidualNaturality、FiniteDimensionalExtEquivalence | mapping coneから実際Ext接続の自然性・双対分解比較射とcanonical評価の自然性・左右二重Ext自然同型・実際Ext³反変同値 | 有限次元Abelian部分圏・成分線形双対・有限区間のcoherenceとAS周期性も完成 |

| 有限次元Abelian部分圏と線形双対 | FiniteDiagramClosureMaps、FiniteDimensionalAbelian、SmallVectorDuality、ModuleVectorDuality、FiniteDimensionalVectorDuality、FiniteDimensionalNakayama | 左右有限次元Abelian圏・有限極限/余極限の閉性・成分線形双対の自然な反変同値・Ext³との合成による線形exactな自己同値 | 総空間のベクトル双対比較・全作用適合性、頂点/有限区間の移送と射影被覆は完成。区間coherence・AS周期性は完成。左右総正則Ext比較・全作用適合性まで完成。標準RHomへの接続 |

| 左有限次元加群の総正則Ext比較 | LeftHomColimits、LeftFiniteExtColimits、LeftRegularCoproduct、LeftFiniteRegularExtComparison、LeftRegularTotalAlgebra、RegularLeftModule、LeftRegularExtComparison、RegularRightMultiplication、LeftFiniteTotalExt | 有限生成射影Hom・全次数Extの直和交換、実際の総正則局所単位付き左加群と全右乗法、全次数Extのk線形比較・全右作用適合性 | 標準RHomの符号・shift/derived/perfectへの接続 |

| 実際の道評価と積の商・代数核 | UnrolledPathIndecomposables、ZAlgebraHomomorphisms | 長さ2以上の道は積の商で零。頂点固定Homomorphismの核の左右積閉性・対角零性・成分商同型 | 全射の核の平方への包含は単位41で完成。最小関係は未証明 |

| 道代数提示の核・平方と実際の商 | UnrolledPathArrowClasses、FreeLinearKernelSupport、UnrolledPathKernelSquare、LinearIdealProducts、UnrolledPathFiltration、UnrolledPathIdeals、ASPresentationKernel、QuotientZAlgebra、ZAlgebraIsomorphisms、ASPresentationQuotient | 長さ1の類の独立性・核の長さ2以上支持性、実際の矢イデアル平方との一致、ASRegularから(1.9)、実際の商代数・商射・第一同型定理とAS代数の商同型 | 任意の基底の持上げ・最小関係・選択の独立性 |

| 閉路ポテンシャル・巡回微分とJacobian商 | ClosedPathPotentials、PathWordEmbeddings、PathCyclicDerivativeSupport、PathCyclicDerivatives、CyclicDerivativeDegrees、PathCyclicDerivativeDegrees、CyclicDerivativeCommutators、PathUnrolling、PathDegreeUnrolling、GeneratedLinearIdeals、UnrolledJacobianRelations、UnrolledComponentHeights、UnrolledJacobianAlgebra | 実際の閉路/cut1/長さ≥3ポテンシャル、道を値に取る巡回微分と長さ/次数・(3.8)/交換子恒等式、unrolled Jacobianイデアル・平方包含と実際の商ZAlgebra・関係の零性 | signed微分とLeibnizは単位43で完成。全d²=0・実際のコホモロジー/正則性定義・H⁰の線形Jacobian商比較は単位44で公開検証。積保存・graded Jacobian/unrolling比較・AS対応は未証明 |

| 全Ginzburg複体・実際のH⁰と正則性 | VertexCyclicCommutators、PathCyclicCommutators、GinzburgLoopSquare、GinzburgSquareZero、GinzburgCochainComplex、GinzburgRegularity、PathLinearIdeals、GinzburgDegreeNegOnePaths、GinzburgBoundarySpaces、GinzburgBoundaryProducts、PathJacobianIdeal、GinzburgDualContexts、GinzburgJacobianBoundaries、GinzburgHomologyZero、GinzburgTotalHomologyZero、GinzburgPositiveHomology | 全d²=0、mathlib成分/全cochain複体とhomology、有限直和比較、実際の負次数消滅によるGinzburgRegular、正次数零性、真のJacobianイデアル＝境界、成分/全H⁰のJacobian商空間との線形比較 | H⁰積保存、cut/unrolling商比較、特定Φの正則性とAS条件との両方向対応、標準双加群分解・3-CY |

| 固定cut複体とgraded H⁰比較 | GinzburgPathFiniteness、GinzburgCutCochainComplex、GinzburgCutProjections、GinzburgCutRetracts、GinzburgCutBounds、PathCutGrading、PathJacobianGrading、GinzburgCutDegreeZero、GinzburgCutHomologyFinite、GinzburgCutHomologyZero、UnrolledPathWords、PathCutUnrollingEquiv、GinzburgCycleBoundary、GinzburgCutDecomposition、GinzburgCutRegularity | 固定cut項/homologyの有限次元性と具体的有界性、実際のretractとcycle/boundary判定、全正則性と全cut負次数消滅の同値、Jacobianのhomogeneous閉性、固定cut H⁰との線形同型、unrolling/eraseの道/線形同型 | 商のunrolling交換・H⁰積保存、AS条件との対応 |

| Jacobian商とunrollingの交換 | UnrolledPathErasure、UnrolledJacobianErasure、PathCutUnrollingComparison、UnrolledErasureIdeals、UnrolledJacobianIdealErasure、PathJacobianContexts、PathCutProducts、PathJacobianHomogeneousContexts、PathQuotientProducts、PathBetweenSheets、BetweenSheetLinearEquiv、UnrolledJacobianLiftIdeal、UnrolledJacobianContexts、BetweenSheetJacobianIdeals、JacobianUnrollingQuotient、JacobianCutQuotientProducts、JacobianUnrollingProducts | 任意整数sheet差の道/線形同型と積保存、真のhomogeneous Jacobianイデアルと実際のunrolledイデアルの一致、商のunrolling交換・homogeneous商積保存、固定cut H⁰とA(Φ)成分の線形比較 | H⁰そのものの積、全単位的Jacobian環、正則性/AS対応と標準双加群分解 |

| 実際のH⁰の代数構造 | GinzburgZeroProducts、GinzburgZeroQuotientProducts、GinzburgHomologyZeroProducts、GinzburgJacobianProducts、GinzburgCutZeroProducts、GinzburgCutZeroQuotientProducts、GinzburgCutHomologyZeroProducts、GinzburgCutJacobianProducts、GinzburgCutHomologyUnits、GinzburgHomologyZAlgebra、FiniteComponentAlgebra、PathJacobianRing、FiniteComponentAlgebraEquiv、GinzburgHomologyUnits、GinzburgHomologyRing、PathJacobianRingQuotient | 微分からのboundary閉性・実際のH⁰積/単位元/結合則、Jacobian/A(Φ)比較の積保存、整数添字H⁰代数同型、全単位的環と全環商・H⁰成分環AlgEquiv、全mathlib H⁰表示 | augmentation/quasi-isomorphismは単位48で完成、標準双加群/単純分解・GinzburgRegular/AS対応は未証明 |

| 実際のaugmentationとfree-generator complex | HomologyAugmentation、GinzburgAugmentation、GinzburgCutAugmentation、GinzburgUnrolledAugmentation、GinzburgLastGenerator、GinzburgAugmentationBasis、GinzburgAugmentationIdeal、GinzburgLastGeneratorGradings、GinzburgAugmentationGradedFree、GinzburgAugmentationComplex、GinzburgAugmentationHomology、GinzburgAugmentationRegularity | canonical augmentationのquasi-isomorphismとGinzburgRegularの同値、実際の有限free-generator表示と次数移動・signed微分閉性、augmentation complexのGinzburgRegularからの負次数homology零性 | 3層のprefix complex比較、A(Φ)上の標準単純分解のexactness、Ext表/AS対応 |

| 実際の3層filtrationとprefix cochain比較 | FinsuppSupportedQuotient、GinzburgGeneratorFiltration、GinzburgGeneratorFiltrationDifferential、GinzburgGeneratorFiltrationBounds、GinzburgGeneratorLayers、GinzburgGeneratorLayerQuotients、GinzburgGeneratorFilteredComplex、GinzburgAssociatedGradedComplex、GinzburgGeneratorLayerBasis、GinzburgLastGeneratorDifferential、GinzburgGeneratorPrefixComplex、GinzburgGeneratorPrefixHomology、GinzburgGeneratorLayerCoefficients、GinzburgGeneratorLayerClasses、GinzburgGeneratorShiftAppend、GinzburgGeneratorLayerComparison、GinzburgGeneratorAppendCoefficients、GinzburgGeneratorLayerInverse、GinzburgGeneratorLayerHomology、GinzburgGeneratorLayerConcentration、GinzburgGeneratorLayerAugmentation | 実際の隣接商とfinite signed-prefix complexesのcochain同型、正則性から各層homologyの生成元次数への集中、canonical augmentationのquasi-isomorphism | A(Φ)係数比較、filtration長完全列、標準単純分解とExt表/AS対応 |

| 実際のfiltration長完全列と3項homology複体 | GinzburgGeneratorFiltrationShortExact、GinzburgGeneratorFiltrationHomologySequence、GinzburgGeneratorFilteredAugmentation、GinzburgGeneratorFiltrationSyzygy、GinzburgGeneratorUpperFiltration、GinzburgGeneratorFiltrationKernel、GinzburgGeneratorFiltrationRadical、GinzburgGeneratorFiltrationCokernel、GinzburgGeneratorPrefixTopQuotient、GinzburgGeneratorHomologyComplex | 実際の短/長完全列とkernel/cokernelの普遍性、3項homology chain complexと正則性からのaugmentation quasi-isomorphism、actual prefix top homology quotient | A(Φ)係数・射影項の同定、A線形性/標準分解微分との照合、Ext表/AS対応 |

| 実際の層homologyとAS射影項の評価成分 | GinzburgGeneratorPrefixDifferentialCoefficients、GinzburgGeneratorPrefixBoundaryFamily、JacobianOriginSheet、GinzburgGeneratorPrefixJacobian、GinzburgGeneratorIndices、GinzburgGeneratorCoefficientIndices、GinzburgProjectiveTermComponents | actual boundary pi quotientと全integer sheetのA(Φ)有限族の同型、生成元族/終点対応、実際のTerm₁/Term₂/representableの評価成分同型 | A線形性/自然性、接続写像・標準微分、augmentation H⁰/radical、単純分解/Ext表/AS対応 |

| augmentation radicalと四項成分複体 | GinzburgAugmentationHeight、RepresentableRadicalComponents、GinzburgAugmentationHeightHomology、GinzburgAugmentationRadical、GinzburgASComponentDifferentials、GinzburgASComponentExactness、GinzburgASComponentComplex | 正則性なしの実際のaugmentation H⁰/radical成分同型、射影項の成分写像とexactness、正則性から四項成分複体/単純商augmentation quasi-isomorphism | A線形性/自然性、標準微分、最小性、右加群の実際のAS分解/Ext表/AS対応 |

| 実際の道作用とfiltration/prefix homology自然性 | GinzburgFilteredLeftAction、GinzburgAssociatedLeftAction、GinzburgFiltrationLeftNaturality、GinzburgGeneratorDifferentialNaturality、GinzburgPrefixLeftAction、GinzburgPrefixComparisonNaturality、GinzburgLayerHomologyNaturality、ModuleCatCokernelHomologyNaturality、GinzburgPrefixTopNaturality、GinzburgPrefixTopHomologyNaturality、GinzburgPrefixFamilyClasses | 実際のdegree0 path chain maps/δ自然性、append比較と逆homology同型、top homology quotient自然性とclass係数 | A(Φ)積作用/全加群の射、標準微分/最小性、AS分解/Ext表/AS対応 |

| Ginzburgからの実際の有限単純射影分解 | GinzburgASProjectiveResolution、GinzburgSimpleProjectiveDimension、GinzburgSimpleFiniteProjectiveResolution、GinzburgSimpleExtColimits、GinzburgASEndpointMinimality | 本来のGinzburgRegularからactual simple ProjectiveResolution、有限生成射影全項、Ext≥4零/PD≤3、actual Ext余極限/直和交換、D₁/D₃最小性 | 他の低次数/非対角Ext零性、AS総rank=1とASRegular(ii)、actual双対左複体の比較 |

| Ginzburgからの最小AS分解と本来のExt | GinzburgASMiddleMinimality、GinzburgMinimalASResolution、GinzburgMinimalResolutionExt、OppositePotential、OppositeGinzburgGeneratorDifferential | original Φ条件からD₂最小性、本来のGinzburgRegularからASResolution(i)、actual Ext³≃k/全次数有限性/総rank≥1 | 他のExt消滅・総rank=1/ASRegular(ii)、actual dual左複体 |

| actual反対Jacobianと左右線形加群 | OppositeGinzburgCochainIso、OppositeReflectedJacobianIso、OppositeJacobianLinearEquivalence、OppositeJacobianExactness、OppositeJacobianRepresentables | native反対正則性同値、反射ZAlgebra/線形左右加群圏同値、exactness/representable比較 | native右dualと左分解の微分比較/ASRegular(ii) |

| native左単純分解とactual Hessian | GinzburgLeftSimpleProjectiveResolution、GinzburgLeftFiniteProjectiveResolution、GinzburgLeftSimpleExtBounds、PathCyclicHessian、OppositePathCyclicHessian、GinzburgDualOriginalClassFormula、GinzburgProjectiveConnectingClasses | GinzburgRegularから全左単純のfinite genuine ProjectiveResolutionとExt≥4零性、actual Hessian反転/正長さ/cut支持とnative射影D₂ class公式 | 標準基底行列、dual/左分解の微分一致と低次数/非対角Ext零性/ASRegular(ii) |

| native射影classと恒等元基底 | GinzburgLayerHomologyClasses、GinzburgDualCoefficientRepresentatives、GinzburgLoopCoefficientRepresentatives、GinzburgLoopProjectiveConnectingClasses、GinzburgPrefixFamilyUnits、GinzburgSingleGeneratorProjectiveBasis | 全native D₂/D₃代表元とclass公式、actual prefix単位・既存射影基底の一致を全体検証 | canonical右A-dualと反対分解の全微分一致、低次数/非対角Ext零性・ASRegular(ii) |

| native全射影行列とcanonical A-dual | GinzburgGeneratorJacobianEntries、GinzburgADualMatrixFormulas、GinzburgFirstProjectiveClasses、GinzburgFirstProjectiveBasis、GinzburgFirstProjectiveYoneda | native D₁/D₂/D₃のactual Yoneda行列とD₂/D₃のcanonical A-dual行列を全体検証 | canonical右A-dualと反対分解の全微分一致、低次数/非対角Ext零性・ASRegular(ii) |

## 主結果の状態

| 主張 | 状態 |
|---|---|
| 定理3.2：一般の型QのAS–Ginzburg対応 | 未証明。形式的な定理文も未実装 |
| 命題1.3 | 既存モデルの数値的両方向とExt成分の左単純商への同型は証明済み。全次数の直和交換と成分作用適合性は証明済み。総代数・左右総作用と具体的局所単位付きGr(A)モデルへの圏同値は完成。全次数のk線形Ext同型は完成。前合成・後合成の自然性は完成。単純加群の(1.12)の左作用を含む移送は完成。一般有限次元右MのExt(M,A)比較と全左作用への適合性も完成。左側の総正則Ext比較と全右作用適合性も完成 |
| 命題1.4：AS条件からの周期性 | 証明済み。ASRegular.nakayamaWindowSystemから正負の周期同型を構成。周期性を入力条件に追加していない |
| 命題5.1：三周期性 | TrianglePeriodicityでASRegular triangle333から正負3周期性は証明済み。§5のquadratic最小分解(5.1)との三重coproductの比較は未証明 |
| 系5.2：(3,3,3)型の全単射 | 未証明。形式的な定理文も未実装 |

## 条件付き結果と残る義務

ASResolutionの存在は原論文定義(i)の条件をモデル化したもの。任意のAで導いたとは扱わない。
ASRegularの条件には周期性・WindowSystem・delta型のExt表・主定理相当の結論を含めない。
数値Ext表とcoherentなWindowSystemはAS条件から導いている。幾何的な共役・tilting・CY completionへの入力を原論文から導く証明義務は残る。
標準無限分解だけから有限性を主張しない。
古いleftDerived型ExtのisoExtを新しいAbelian.Extの比較定理と取り違えない。

- Gr(A)モデルとの左右圏同値とAbelian構造は完成。実際のExt保存と自然性も完成。正則加群の同定と(1.12)への移送。
- 全M,N・全次数の自然なHom複体–Abelian.Ext比較。命題1.3の3次比較は証明済み。
- A-dual・左単純商の同型、全次数Extと直和の交換、成分左作用への適合性は完成。総代数・局所単位付き加群との圏同値・Abelian構造は完成。実際の全次数Ext保存と自然性も完成。正則加群の同定と全左作用を保つ実際のExt移送は完成。(1.12)の左加群の束ねと次数3の同型が次の義務。
- 有限長Ext双対性と区間coherence、AS条件からの正負周期性は完成。左側総正則Ext比較は完成。道代数提示と標準RHom/derived/perfectへの接続を続ける。
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

前回ext-sums時の優先課題だった総代数・左右圏同値と自然な全次数Ext保存は完成。現在は正則右加群の同定と(1.12)への移送を進める。
今回8単位の対応・仮定・利用先はdocs/ext_coproduct_exchange.md。
差分・検査・実測時刻・main保存先はRECENT_RUN.mdとruns/ext-sums-20261008.md。
初期14モジュール、開始時51モジュール、PDFと歴史的な487ファイルの保存確認はverification/ext_sums_preservation.json。
前回の数値的同値・左双対の証拠はverification/as_finiteness_github_ci_evidence.jsonと同名のCI logに保持。
今回の正確な数学headのCI・artifact成功を確認済み。RECENT_RUN.mdとverification/ext_sums_github_ci_evidence.json参照。

前回ext-sumsの数学コミット6666e09の[main CI](https://github.com/uedakazushi/as-ginzburg-lean/actions/runs/37737755500)はsuccess。
636異なる宣言・全274 theoremの新規監査、全7段階終了0、12ファイルのartifact 11532667814保存を確認。
CI検証UTC 2026-10-08T06:28:37.911543+00:00 → 2026-10-08T06:36:04.010329+00:00、単調時計446.098779473秒、終了0。
証拠はverification/ext_sums_github_ci_evidence.jsonと同名のCI log。
この確認後の終了記録の保存は文書・ログのみ。同じ数学ソースを保持し、そのpushも新規CIを開始する。
