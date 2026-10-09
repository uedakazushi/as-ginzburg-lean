# AS–Ginzburg Lean: 継続作業の規約

2026-10-09のユーザー指示：GitHub Actionsの予算節約のため、GitHubでのビルドは最小限にする。
通常の検証済みmain保存コミットには`[skip ci]`を付ける。Leanビルド・全宣言公理監査・検証証拠保存は作業環境で継続する。
GitHub Actionsの再実行・新規実行は通常の保存では開始しない。
検証workflowは手動実行（`workflow_dispatch`）のみとし、必要時に限って使う。

## 最初に読むもの

`HANDOFF.md`、`STATUS.md`、`GAPS.md`、`verification/results.json`、
`recovery/recovery_results.json`、`RECENT_RUN.md`を読み、最新の`verification/latest.json`が
指す実行の`run.json`と終了コードを確認する。旧成功記録だけで現在の成功を宣言しない。数学的作業では`docs/source.pdf`も読み、
原論文と既存定義の対応を先に確認する。

## 固定環境と検証

- Lean: `leanprover/lean4:v4.24.0`。
- mathlib: `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`。
- `lake-manifest.json`の全依存コミットを保つ。通常の再現に`lake update`を使わない。
- Python 3、Git、bash、elanまたは固定Leanの配布物を使う。
- 初回は`bash scripts/check.sh --prepare-cache`。依存キャッシュがあれば`bash scripts/check.sh`。
- 固定LeanがPATH外なら`AS_GINZBURG_LEAN_ROOT=/path/to/lean-4.24.0-linux bash scripts/check.sh --prepare-cache`。
- スクリプトは`bash`からも実行でき、`check.sh`と`with_lean.sh`の実行権限をGitに記録する。
- 回帰テストだけなら`python3 -m unittest discover -s tests -v`。
- 毎回新しい`verification/runs/<run-id>/`を作り、実行環境、宣言一覧、`lake build`、
  全明示的宣言の`#print axioms`、終了コード、UTC開始・終了時刻、単調時計の経過秒を保存する。
- 許容公理は`propext`、`Classical.choice`、`Quot.sound`のみ。
  `sorry`、`admit`、独自`axiom`、`sorryAx`、`Lean.ofReduceBool`、`Lean.trustCompiler`は認めない。
- 宣言名・監査コマンド・監査ログの重複、監査漏れ、未対応の宣言構文は失敗とする。
  件数161は初期成果の記録であり、将来の宣言数を固定しない。

## 数学的範囲

定理3.2と系5.2は**未証明で、Leanの形式的な定理文も未実装**。
命題1.4のAS条件からの正負周期性は証明済み。命題5.1も含め、主定理の同型類対応は未証明。
初期84補助定理やビルド成功を主定理の完成と扱わない。

2026-10-08のユーザーの明示的な指示により、既存`ZAlgebra.RightModule`の
Abelian圏構造とmathlibのホモロジー代数への接続を実装する数学的形式化を再開し、
既存のpresheafモデル上で完成した。さらに射影性・EnoughProjectives・radical・s_v・
標準射影分解と実際のExtの存在まで完成した。その後、一般radical・minimality、
有限AS分解のmathlib ProjectiveResolutionへの変換、実際Extの線形性・次元シフト、
具体的ASRegular定義と数値的AS双対性の順方向まで完成した。
その後、有限AS分解だけからExtの全次数有限性と高次消滅、数値条件の逆方向、
具体的左加群・左単純商・Ext成分左加群の同型、Hom/Ext⁰の余極限交換、
左側のEnoughProjectivesと実際のExt、左右のrepresentableの二重A-dualの対象同型も完成した。
一般のcanonical評価写像と自然性、representableでの評価の同型性も完成。有限生成射影を実際の有限直和の直和因子として定義し、左右のcanonical評価同型も完成。双対の閉性と左右の有限生成射影部分圏の反変同値も完成。任意形状の複体・ホモトピー圏と有界性の保存、その部分圏の反変同値も完成。cochain次数反転と有界cochainホモトピー圏の反変同値、AS分解の項の有限生成射影性と有界[-3,0]cochain複体への持上げも完成。標準RHomの符号・shift/derived接続、perfect complexへの拡張は未証明。
その後、有限AS分解から全次数Extと小さい直和の交換、左右の忠実exactな総空間関手、
直和上の行列作用とExt交換同型の全A.Hom成分左作用への適合性まで完成した。
左右総空間について、任意の有限個の元が恒等成分作用の有限和により固定されることも証明済み。
有限台の忠実正則表現・非単位的総代数・共通両側局所単位と、左右総空間への実際の総代数作用も完成した。
単位化ModuleCatの具体的な局所単位付き部分圏と、左右総加群の所属の証明も完成した。
射・左右総加群関手と忠実性も完成した。
左右総加群関手の充満性も完成した。
任意の単位化上の左右加群の成分作用と直交冪等な成分射影も完成した。
射影像からの成分加群の対象復元も完成した。
成分射の復元関手と局所単位条件からのk線形直和分解も完成した。
全単位化作用への適合性・自然性・単位と余単位、具体的局所単位付きGr(A)モデルとの左右圏同値も完成した。
局所単位付き加群圏のAbelian構造・EnoughProjectives・実際のExtの存在と、左右関手のk線形性も完成した。
導来圏の同値を通じた全M,N・全次数の実際のExtのk線形保存も完成した。
前合成・後合成の自然性も完成。正則総空間の線形同型と右乗法との一致も完成。
正則総加群の加群同型・成分左乗法との一致も完成。
全総代数の左乗法、実際のExt移送と全左作用への適合性も完成。
実際のExtの局所単位付き左加群を構成し、AS条件から原論文(1.12)の
次数3の左単純商同型と他の全次数の零性も完成。
canonicalな二重双対は有限生成射影・有界cochainホモトピー圏まで完成。AS条件の実際Ext消滅から双対複体の低次数exactness・Ext³上端余核を証明し、全左単純加群の四項ProjectiveResolutionと各項の有限生成射影性・次数4以上零性も完成。canonical二重双対複体の同型と一般ProjectiveResolutionのsyzygy・Hom複体を用いた実際Ext消滅の接続も完成し、左単純の全次数Extが3次以外で零であることを証明した。左側の実際Extの自然な長完全列と右成分加群、Ext³左単純≅右単純および全左単純の他の全次数の零性も完成。左右有限次元加群の実際のfiltrationとExtの3次集中、Ext³の有限次元性と反変短完全列、full部分圏へのk線形反変関手、射影次元≤3と第3 syzygyの射影性も完成。有限生成射影表示・有限直和と拡大の閉性・snake lemmaによる核の貼り合わせ、AS条件から左右有限次元加群の長さ3の有限生成射影分解の存在も完成。全項有限生成射影の実際の四項ProjectiveResolutionと次数4以上零性、一般Hom複体のexactness、有限生成射影Homと左右有限次元加群の全次数Extの余極限・直和交換も完成。一般有限次元右加群の総正則Ext比較と全左作用への適合性、左右有限次元加群の二重Ext対象同型も完成。実際Ext class・接続写像と射影分解比較射の自然性を証明し、左右二重Ext自然同型と有限次元full部分圏の実際Ext³反変同値も完成。左右有限次元Abelian部分圏と成分線形双対の自然反変同値、実際Ext³との合成による線形exactな自己同値も完成。頂点単純のτ⁻¹移送、有限区間Abelian部分圏と包含のexactness、組成列による一般加群の区間台の負方向移送も完成。逆関手の台保存と線形exactな区間制限同値、実際の切詰めrepresentableの射影被覆・本質性・End=kと正規化した移送同型も完成。切詰めrepresentable間のHomによる代数成分回収と単位元/積保存、下端変更の実際の全射と自然性、被覆の対角成分同型と後合成単射性も完成。正規化した移送の区間coherenceとAS条件からの正負周期性も完成。総空間のベクトル双対とのcanonicalな自然比較・全総代数作用への適合性も完成。有限区間関手・単純同型の包含比較、右加群圏でのNakayama射の合成保存と正規化した被覆の実際の加群同型まで完成。区間coherenceとAS条件からの正負周期性は完成。左側総正則Ext比較と全右作用適合性も完成。
単位40でd₁からのincoming係数・実際の自由道ZAlgebra全射、(1.8)の最小生成元の次元式と基底、(1.10)の成分分解まで完成。単位41で核の矢イデアル平方への包含と実際の道代数商同型まで完成。任意の基底の持上げ・最小関係・選択の独立性は未証明。
単位42で実際の閉路ポテンシャル・道を値に取る巡回微分・長さ/次数・(3.8)/交換子恒等式、unrolled Jacobianイデアルと実際の商ZAlgebraまで完成。単位42時点ではGinzburg dg微分・d²=0・正則性は未実装であった。ASRegular triangle333から正負3周期性は証明したが、§5の通常のquadratic分解との比較は未証明。
単位43で実際の拡張道代数・生成元微分とsigned線形延長、Leibniz則・次数/cut/winding保存まで公開検証。単位44で全生成元/全道/全有限線形結合のd²=0、実際のmathlib複体・成分/全homology、実際の負次数消滅によるGinzburgRegular定義と正次数零性、真のJacobianイデアル＝境界、成分/全H⁰のJacobian商空間との線形同型まで公開検証。H⁰の積保存、cut/unrolling商比較、特定のΦの正則性とAS条件との両方向の対応は未証明。
単位45で固定cut項とhomologyの有限次元性・具体的有界性、複体/homologyのretractと有限射影和による全正則性のcut成分判定、homogeneous Jacobianイデアルと固定cut H⁰の線形比較、unrolling/eraseの道/線形同型まで公開検証。AS条件との同値と商のunrolling交換・H⁰積保存は未証明。
単位46で任意整数sheet差の道/線形同型・積保存、実際の巡回微分の持上げ/忘却、同次数context spanと全sheetの関係の積閉性から真のJacobianイデアルのunrolling対応、商同型とhomogeneous商積保存、固定cut H⁰≅A(Φ)成分の線形同型まで公開検証。H⁰そのものの積・全単位的環・正則性/AS対応は未証明。
単位47で実際の微分からboundaryの左右積閉性・通常/固定cut mathlib H⁰の積/ゼロ道単位元/結合則、Jacobian/A(Φ)比較の積/単位元保存、整数添字H⁰ ZAlgebra同型、全単位的道環/Jacobian環と真の全環商同型、H⁰成分環AlgEquivと全mathlib H⁰の加群表示まで公開検証。canonical augmentation/quasi-isomorphism・標準双加群/単純分解・正則性/AS対応は未証明。
単位48で一般Abelian圏のcanonical homology augmentation/quasi-isomorphism判定、通常/固定cut/unrolled Ginzburg augmentationとGinzburgRegularの同値、実際のaugmentation idealの最後の生成元による自由有限和表示・次数移動・signed微分閉性、mathlib augmentation complexとGinzburgRegularからの負次数homology消滅まで公開検証。3層のprefix complex比較、A(Φ)の実際の標準単純分解のexactnessとExt表/AS対応は未証明。
単位49で実際の最後の生成元による3層filtration/subcomplexesとsigned微分閉性、隣接商のassociated-graded complexesを構成し、実際の道の係数・生成元付加・Leibnizから全有限signed shifted-prefix complexesとのcochain同型を証明した。GinzburgRegularから各層のhomologyが生成元次数だけに集中し、その実際のhomologyへのcanonical augmentationがquasi-isomorphismとなることも公開検証。A(Φ)成分との比較、filtration長完全列からの標準単純分解のexactnessとExt表/AS対応は未証明。
単位50で実際のfiltration短完全列とmathlib長完全列、F_-2とaugmentation複体の同型、正則性から最初の接続写像の同型、F_0と第0層の同型・homology集中、実際のloop→dual射のkernel普遍性、正則性を仮定しないaugmentation homologyへの全射/cokernel普遍性を証明した。実際の3項homology chain complexとGinzburgRegularからのaugmentation quasi-isomorphism、prefix top homologyのactual differential imageによる商表示まで公開検証。各項のA(Φ)係数/射影加群への同定とA線形性・標準単純分解の微分との照合、Ext表/AS対応は未証明。この複体をA(Φ)標準射影分解の完成とは扱わない。
単位51で実際のsigned prefix微分の係数と境界族の一致、finite quotientPiによる各層top homologyのJacobian/A(Φ)成分有限族への同型、任意整数origin sheet、0/−1/−2生成元とincoming/outgoing/loopおよびprefix終点の対応を証明し、既存有限coproductの同型から各層homologyと実際のAS射影項の評価成分の線形同型まで公開検証。ASResolutionの存在を仮定しない比較である。加群圏の自然性・A線形性、接続写像と標準微分の照合、augmentation H⁰/radical、標準単純分解/Ext表/AS対応は未証明。評価成分の同型を加群としての自然同型の完成とは扱わない。
単位52で実際の道のwinding/高さ差からaugmentation成分の高さ判定と全cochain/homology同型/零性、既存representable radical成分との比較を証明し、augmentation H⁰≅radical評価成分を正則性なしで完成した。実際のfiltration接続写像を既存AS射影項の成分へ移し、平方零性・radical全射・各短複体のexactness、GinzburgRegularから左端単射を証明。実際の四項成分chain complexと真の単純商へのaugmentation quasi-isomorphismまで公開検証。加群圏での自然性/A線形性・標準微分との一致・最小性・実際のAS分解とExt表/AS対応は未証明。成分ごとの複体をASResolutionの存在とは扱わない。
単位53で実際のdegree0道のfiltered/associated/prefix chain maps、inclusion/quotient適合性、短完全列の射とmathlib δの自然性、loop→dual/dual→originalの自然性を証明した。生成元付加比較と逆cochain/homology同型、actual prefix top homologyとincoming-boundary quotient比較の自然性、finite quotient族のclass係数まで公開検証。A(Φ)成分の積作用との比較、全右加群の射/自然性、標準微分・最小性・実際のAS分解/Ext表/AS対応は未証明。未解決chain termsへのJacobian商作用は仮定していない。
単位54〜59で固定endpointのactual A(Φ)係数比較と積作用、全RightModule morphismsへの自然性、augmentation H⁰/radical自然性を完成した。実際のD₁/D₂/D₃による四項射影複体と単純商augmentationを構成し、本来のGinzburgRegularからmathlibのgenuine simple ProjectiveResolutionと全項の有限生成射影性を証明した。実際のsyzygyとExt長完全列から任意標的への次数4以上のExt零性・射影次元≤3、全次数Extとexact colimit/小さいcoproductの交換を導いた。D₁/D₃の最小性はactual radical因子分解とendpoint高さから完成。D₂の最小性、既存minimal ASResolution、標準巡回微分行列/双対左複体の比較、Ext³のAS左単純同型とASRegular全体は未証明。直和交換・周期性・AS結論を新しい仮定に追加していない。定理3.2/系5.2は未証明・正式Lean定理文未実装。
単位60〜65で元のPotentialの長さ≥3からactual巡回微分/境界の長さ≥2、prefix係数とnative filtration接続写像のrepresentativesを証明した。actual D₂のradical包含を導き、全3微分の最小性・exactness・左端Monoから、本来のGinzburgRegularだけで既存ASResolutionの全フィールドを構成した。ASRegularの分解条件(i)は完成。実際のExt³(s_(τv),P_v)≃ₗk、rank/finrank=1、全単純/representable/全次数のExt有限性とAS総rank≥1も完成。総rank=1/他の低次数・非対角Ext消滅/ASRegular(ii)は未証明。反対箙を矢/頂点順/sheetの反転から構成し、actual道・閉路cut=1/長さ≥3のPotential空間同値、積反転、actual巡回微分の反転を証明。拡張Ginzburg道の同値と3次数保存、生成元微分の(-1)^(degree+1)付き比較まで公開検証した。周期性/Ext表/Calabi–Yau性/主結論を新しい仮定にしていない。定理3.2/系5.2は未証明・正式Lean定理文未実装。
単位66〜70で全道/全homogeneous sumsの微分反転と三角数signによるactual cochain/homology同型を証明し、native反対GinzburgRegularとの同値と反対最小ASResolutionを完成。actual Jacobianイデアルとcut/sheet商の反対同型、全整数成分での積反転・単位元保存、反射ZAlgebra同型を完成。既存の線形左加群圏と反対Jacobianの既存線形右加群圏の線形同値を構成し、両方向のexactness/短完全列の保存、left representable at i≅right representable at n-1-iのactual加群同型まで全体検証した。周期性/Ext表/Calabi–Yau性/主結論を新しい仮定にしていない。
単位71〜79でactual反対Jacobian圏同値による単純商/representableの逆像同型と全評価成分比較を証明。native反対GinzburgRegularから全整数iの元の左単純加群のgenuine ProjectiveResolutionを構成し、全項の既存有限生成射影性・長さ3のfinite cover列・射影次元≤3・任意標的への次数4以上Ext零性を完成。actual巡回微分交換子恒等式からmixed係数一致を導き、native word/path Hessian、元のPotentialの長さ≥3から正の道長さと本来のcut支持、反対ポテンシャルの転置/道反転を証明。actual Ginzburg differentialとHessianの全係数、dual矢の上層prefix成分全体とembedded path Hessianの一致、actual degree -1代表元のquotient/differential cycle、native δのclass公式と既存射影第2微分の各評価成分のactual prefix quotient class公式まで全体検証した。周期性・必要Ext表・Calabi–Yau性・ASRegularを追加仮定にしていない。
単位80〜91で、全層のactual homology/projective class係数と全dual/loop射影項の代表元の全射性を証明。native loop→dual接続写像のactual differential quotient class、ループ微分のword/path係数、全filtered層のprefix係数、nativeループ微分のdual prefix成分全体＝original arrow、既存射影第3微分の全評価成分のactual class公式を完成。actual零道商類とrepresentable恒等成分、有限prefix単位族とcoproduct恒等元基底、actual単一矢/ループ代表元とnative射影基底の同定まで全体ビルド・全宣言公理監査で検証した。
単位92〜113で、native D₂のactual Hessian行列とnative D₃のactual original矢行列、全有限representable coproductのYoneda座標とcanonical A-dualのtranspose公式を完成。native D₁をactual filtered inclusionのhomologyMapと照合し、mathlib cycle classと実際の境界商classの一致、全filtered代表元のJacobian商公式、original単一矢の恒等元基底とD₁のYoneda行列まで全体ビルド・全宣言公理監査で検証した。
公開132〜213は全体検証済み。本来のGinzburgRegularから元のASRegular全体、foundationへのexact制限と実際のProjectiveResolution/単純射影次元≤2/高次Ext消滅、真のI/(IJ+JI)とcategorical AS核radical商の全成分同型、最小関係基底と実際の持上げ・mod分解生成性まで完成。
214〜242の29数学モジュールは新しい全体ビルド・全宣言公理監査を含め実終了0で検証済み。元のASRegularから原論文の候補ΦB=Σ[ρrρ]を本来のPotential型で構成し、cut微分=選んだrρ、unroll後の元の表示核と最小関係商類、有限高さ差帰納法による第零sheet全表示核の実際の関係イデアル生成性を証明。225の一般補題の条件は227で元のASRegularから導出済み。有限FoundationAlgebra反対環ModuleCatへの総加群関手と冪等成分回収関手も構成済み。
243〜275の33数学モジュールは個別Lean実終了0・診断なし、2バッチの116宣言公理監査成功後に公開ソースへ統合し、692モジュールの新しい全体検査も全6段階実終了0で完了。元の成分抽出とPi.singleによる線形同型/元A.Hom作用適合性から単位自然同型を構成。直交冪等射影の単位和から任意環加群の実際の有限成分和復元、全行列成分分解から全環作用適合性と余単位自然同型を証明。既存FoundationRightModuleと実際FoundationAlgebra反対環ModuleCatの圏同値、両関手のk線形性、EnoughProjectives/HasExtと全対象・全次数の実際Extのk線形保存まで完成。AS制限単純の実際環射影分解、元ASRegularから環モデルの射影次元≤2/任意標的へのExt≥3消滅まで完成。単位256〜268で元AS表示の実際有限環全射、本来の最小関係成分イデアルによる環商AlgEquiv、非cut自由道環と第零sheet自由道環の単位/積保存AlgEquiv、本来の関係イデアルを引戻した非cut環商から元foundation環の回収を証明。選んだ非cut関係と元の最小関係持上げを照合し、窓外の積零性から有限環両側イデアルの成分イデアルへの拡張も証明。必要なExt同型や正則性を仮定にしていない。 単位269〜275で有限行列成分による関係イデアルの正確な生成性を証明し、非cut自由道環と零sheet環のAlgEquivで移送した。候補ΦBのcut微分集合は選んだ最小関係集合と等しく、本来の非cut Jacobian環B(ΦB)≃ₐ元FoundationAlgebraを元ASRegularのみから証明した。追加の関係生成仮定は残っていない。全ZAlgebraの回収とΦBのGinzburgRegularは別の未証明課題である。
WORK243〜264：22数学モジュール/78異なる宣言、UTC2026-10-09T08:58:40.628910+00:00→2026-10-09T08:59:11.273619+00:00、実測30.644710692秒、監査実終了0・厳密照合成功・許容公理3種類のみ・source SHA一致。 WORK265〜275：11数学モジュール/38異なる宣言、UTC2026-10-09T09:21:14.446460+00:00→2026-10-09T09:21:49.701619+00:00、実測35.255161469秒、監査実終了0・厳密照合成功・許容公理3種類のみ・source SHA一致。
WORK276〜290の15数学モジュールは個別Lean実終了0・診断なし。元AS条件から得た周期同型が実際の正次数積部分空間と最小生成元商を保存すること、正負任意回の周期同型とGeneratorIndex移送を証明。sheet 0のAS基底/矢代表元だけを使い、全被覆の実際の矢族、その商類＝移送基底、全自由道表示の全射性/矢イデアル平方核/真の核商≅元AS代数まで完成。元AS条件から283/285/286の具体的基底条件を284で導出済み。零sheet全道・全線形結合・整数成分/有限環表示が元AS表示に一致し、同じ非cut道表示の真の核＝候補ΦBのcut Jacobianイデアル、本来のB(ΦB)≃ₐ元FoundationAlgebraを290で証明。全Jacobian核＝この全表示核、候補正則性、任意整数反復のcoherenceは未証明。真の核商回収をA(ΦB)回収の完成として扱わない。

282のsheet添字同型が既存FoundationArrowBasisの別の同名補題と衝突することを289のimport照合で検出し、foundationSheetGeneratorIndexEquivへ改名。282/284/287/288を現行依存環境で再コンパイルして全て実終了0・診断なし。旧SHAの差分/証拠/失敗ログを無変更保存し、現行証拠へ履歴リンクを追加。草稿監査に公開済み全宣言との重複チェックを追加し、現行281〜290バッチで成功。旧281〜287バッチは旧SHAの歴史的な成功記録として保持し、現行ソースの成功判定には使わない。

WORK276〜280/26異なる宣言：UTC2026-10-09T09:46:04.264805+00:00→2026-10-09T09:46:16.622374+00:00、実測12.357572055秒、監査実終了0・厳密照合成功・許容公理3種類のみ・現行source SHA一致。 WORK281〜290/41異なる宣言：UTC2026-10-09T10:06:07.502943+00:00→2026-10-09T10:06:48.536081+00:00、実測41.033139738秒、監査実終了0・厳密照合成功・許容公理3種類のみ・現行source SHA一致。

現行692数学モジュール/3947異なる宣言/2141 theoremの新しい全体run20261009T092805Z-570508acはsuccess。全6段階実終了0、wrapper0、現行公開ソースSHA完全一致。全宣言#print axiomsを厳密照合し、許容公理propext/Classical.choice/Quot.soundのみ、重複/監査漏れ/holes/独自axiom/禁止依存なし。UTC2026-10-09T09:28:05.391088+00:00→2026-10-09T10:15:36.291672+00:00、実測2850.900579265秒。wrapper UTC09:28:05.355699→10:15:36.300343、実測2850.944647648秒。初期14/開始時60数学モジュール、577保護記録と入力PDFの無変更検査0。243〜275の33数学モジュールの全体検証済み差分を保存し、直接mainへの通常fast-forward保存を準備する。WORK276以後はこの692全体検査対象外。

WORK291〜293は個別Lean実終了0・診断なしで保存。非負sheetの実際の矢代表元の前進周期整合性、実際の周期写像と逆写像の両方向キャンセルまで完成。これらの新しいバッチ公理監査は未実行。WORK294の負sheet整合性は整数表現の依存型変換を調整中で、個別Lean失敗ログを保持し、成功とは記録していない。295の初回検査は294の未生成oleanにより終了1、未完成。零/-1境界と全整数前進整合性は未証明。

未証明：現行FoundationAlgebraのA.{u,u}からu,vへの宇宙一般化、周期整合したfinitecut基底降下、候補ΦBのGinzburgRegularと元の全ZAlgebra回収、Reyes/Hanihara/Keller接続、選択独立性/同型類対応/§5quadratic。非cut関係イデアルのcut微分による生成性と元foundation環の回収は275で完成。条件付き一般生成補題の仮定は270/273/275で元のASRegularから導出済み。候補構成やfoundation環同型を正則性/主定理完成と扱わない。定理3.2と系5.2は未証明・正式Lean定理文未実装。周期性/必要Ext表/Calabi–Yau性/主結論を新しい仮定にしない。
main0076791ff2b0d6c74c05aa2e18ef0a7b871f3467へ214〜242と659モジュール全体成功を通常fast-forward保存済み。243〜275を含む現行692モジュールの新規全体検査は完了、全6段階0。次の通常fast-forwardでこの33数学モジュールと全体検証証拠を直接mainへ保存する。保存後も形式化を継続する。
main0076791のGitHub CI run37911359000は開始済み、最後の取得時点でin_progress。前main6953a852のrun37905210909はsuccess/全7段階実終了0、全文1,382,714bytes/SHA256610d1a4ab83916023ea3151dadedc2d3d5811b0d36a21c6b0565ba9268890e8cとartifact11608860222/digestsha256:f44f260ef65eab396c6f51e024fbb3441b1e976d2a0a98c217fa83406944c8f2を回収済み。UTC2026-10-09T08:29:20.317530+00:00→2026-10-09T09:47:21.221107+00:00、実測4680.903571295秒。前main5c6e119と80eee11のCI全文/artifact証拠も保存。旧成功を新headの成功と扱わない。
任意のAについてAS分解の存在を証明したとは扱わない。
その後の2026-10-08のユーザーの明示的な指示により、射影性・単純加群・実際の分解とExtなど、
残る形式化を自律的に継続する権限を得た。通常の補題・実装方針について繰り返し確認しない。
再開の指示を受けても、原論文の仮定を弱めたり、結論と同等の仮定を追加したりしない。
周期性や`WindowSystem`をAS正則性の条件に追加しない。周期性はAS条件から導く方針を保ち、ASPeriodicityで正負周期性を証明済み。
外部結果を独自公理に置き換えて完成と宣言しない。

## 自律継続と終了条件

数学的形式化の最終目標は、原論文の仮定を保った定理3.2と系5.2の
正式なLean定理文と、その証明の完成である。
必要な外部結果も、証明済みのmathlib定理への帰着または形式化により扱う。
既存の補助定理や条件付き結果を主定理の完成として扱わない。

数学的継続を指示された場合は、最終目標に向けて自律的に作業する。
ユーザーが今回の作業範囲を限定した場合は、その範囲を優先する。

- 補題の完成、ビルド・監査の成功、コミット・push、
  引継ぎ記録の更新だけを理由にターンを終了しない。
- 証明単位を検証・保存した後は、GAPS.mdの次の必要な証明義務へ進む。
- 15〜30分ごとの記録は作業中のチェックポイントとし、
  記録後も継続する。コンテキスト圧縮後も記録から作業を継続する。
- 証明が詰まった場合は、必要な中間補題への分解、mathlibの調査、
  別の証明経路、独立して進められる残課題を検討して作業を続ける。
- 通常の補題、実装方針、検証済み単位のmainへの保存について、
  繰り返しユーザーの確認を求めない。

数学的継続タスクを終了するのは、次の場合に限る。

1. 最終目標を完成し、現在のソースのビルド・公理監査を確認した。
2. ユーザーが停止または作業範囲の変更を指示した。
3. 実際の実行制限、または必要な情報・権限の欠如により、
   利用可能な手段では継続できない。

未完成で終了する場合は、具体的な停止理由、最後の成功検査、
保存済みコミット、未保存差分、次に実行する証明義務を記録する。
実行制限が確認されていない場合、制限による停止とは記載しない。

## 保存とタスク終了時

旧版、入力PDF、`recovery/`、`checkpoints/`を削除・改変しない。
新しいログは既存の実行ディレクトリへ上書きしない。
`FILES.md`と`recovery/original_file_inventory.json`は回収時の歴史的な一覧であり、現行ツリーの一覧ではない。

タスク終了時は`RECENT_RUN.md`とタスク別の`runs/<task-id>.md`に、目的、差分、
実測開始時刻・終了時刻・経過時間、各検査の終了コード、成功した検査、残ったエラー、
コミット・PR・リモート保存状況を記録する。検証所要時間とタスク全体の所要時間を分ける。
測定していない過去の稼働時間は「不明」とし、推測を実測値として書かない。
`README.md`、`HANDOFF.md`、`STATUS.md`、`GAPS.md`を結果と整合させる。
最新のユーザー指示は、PRを新規作成せず、検証済みの証明単位を直接mainへコミット・pushすること。
以前のmainへマージしない方針は、この明示的な指示で置き換えられた。
必要な既存の検証済みブランチをmainへマージできる。force pushや履歴の書換えは行わない。
証明単位ごとに差分・検査・次の補題を保存し、長い作業では概ね15〜30分ごとに現状を記録する。
リモートへ保存できない場合は、理由とGit bundle・差分・最新ログを回収できる形で渡す。
