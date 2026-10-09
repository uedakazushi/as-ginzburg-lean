# AS–Ginzburg対応のLean形式化：Codexクラウドでの継続

## 現行の全体検証成功（2026-10-09T14:35:39.548164+00:00、作業継続中）

公開構成は734数学モジュール/4113異なる明示的宣言/2271 theorem。新規全体run20261009T141039Z-350e971cはsuccess、回帰16件/source監査/固定環境/全体ビルド/全宣言公理監査/厳密報告の全6段階実終了0。UTC 2026-10-09T14:10:39.763026+00:00→2026-10-09T14:33:35.491459+00:00、単調時計の実測1375.728430324秒。全3監査部分も実終了0、全4113宣言の一対一照合とソースSHA完全一致、依存公理はpropext/Classical.choice/Quot.soundのみ。入力PDF・初期14・開始時60・歴史的577保護ファイルも無変更確認0。

統合42モジュールは、元AS条件からの全整数の矢整合性、全道/有限線形評価核の周期移送、全sheetのcut微分とその二側イデアルの表示核への包含、全Jacobian idealのsheet移送を含む。全整数sheetの同じsheet成分で、表示核＝本来の全Jacobian lift idealを証明し、候補Jacobian成分と元AS成分の線形同型・単位・積保存を完成。全自由道代数の整数sheet周期同型も完成。

公開統合後の草稿7モジュール18宣言では、本来の全Jacobian ideal＝erasure pullbackと候補Jacobian代数の整数周期同型、周期反復の自然数加法則、実際のcut次数付き積とその結合性・単位を個別Lean終了0・診断なしで検証。2バッチ公理監査も終了0・厳密照合成功・許容3公理のみ。これら7本は現行734の全体検査対象外で、差分と検証証拠を保存した。

定理3.2と系5.2の正式Lean定理文・証明は未完成。異なるsheetの全代数回収では、選んだ最小関係の代表元とcut矢の選択を対応させる義務が残り、既存の特定表示の全Jacobian核一致を主定理の代わりに仮定しない。候補正則性とReyes/Hanihara/Keller等の導来結果、選択独立性・同型類対応・quadraticへの接続を継続する。検証済み42モジュールを直接mainへ通常fast-forward保存する準備が整った。以下の旧記録はその時点の状態を表す。


## 現行の整数周期・同じsheetのJacobian回収（2026-10-09T14:10:22.591634+00:00、作業継続中）

WORK276〜293の復元18モジュールと新規24モジュール、計42数学モジュールを公開構成へ統合。全整数の前進周期整合性を元AS条件から導き、実際の全道と有限線形結合の評価核の周期保存を証明。候補ΦBの本来のcut微分の全sheet評価零性とその二側イデアルの表示核への包含、全Jacobian idealのsheet shift保存を完成。cut次数0の全Jacobian contextの比較から、全整数sheetの同じsheet成分について表示核＝全Jacobian lift idealを証明。その候補Jacobian成分と元AS成分の実際の線形同型と単位・積保存まで完成。自由unrolled道代数の全整数sheet周期同型も構成。原論文の仮定や必要な結論を新しい仮定にはしていない。

全42モジュールは現行依存環境で個別Lean終了0・診断なし。37/3/1/1モジュール、146/9/6/5宣言の4バッチ公理監査は全て実終了0・厳密照合成功・許容3公理のみ・当該草稿SHA一致。公開済み全宣言との重複照合を実施し、同名補題を改名して依存16モジュールを再検証した。公開importへ切り替えた734モジュールの新規全体検査は進行中で、まだ成功とは記録しない。

旧公開692構成の再検査20261009T130440Z-c3205e18は、数学モジュールのコンパイル後、build内の重複AxiomAudit実行を整理するため明示的に中断し、実終了1/failedとして保存した。初回のキャッシュ失敗2runも保持。検証器は数学ライブラリのビルド後に全宣言#print axiomsを一度実行する構成へ変更し、任意の分割実行でも各実終了コード・厳密照合・全件照合・SHAを認定条件として保持。回帰検査16件は終了0。

異なるsheet間の全Jacobian核の一致、候補GinzburgRegular、必要な外部導来結果、選択独立性・同型類対応・§5quadraticは未完成。定理3.2/系5.2は未証明・正式Lean定理文未実装。同じsheetの成分回収を全ZAlgebra回収として扱わない。全体検証後に通常fast-forwardで直接mainへ保存し、次の数学的義務を続行する。現在のmain保存済みHEADは9ba6b363aa3c2aed832c46f822263df5492170df。


## 現行のB(ΦB)回収・foundation移送表示・検証（単位214〜290）

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

過去の単位説明は当時の状態であり、現在の判定はこの概要と該当SHAの実終了コードを使う。


## 確認済みの代表的な内容

- cut付き有限箙と被覆の頂点、heightの全単射、winding degreeの正値性。
- 道の線形化、双線形な積、局所単位元、結合則。
- 実際の局所有限な正に有向なZ-代数と、そのk線形圏・右表現可能加群。
- 線形Yonedaによる表現可能加群のHomの同定と、逆方向のHomの消滅。
- 既存`RightModule`の(余)極限の閉性、核・余核・有限積とAbelian圏構造。
- 頂点評価による核・余核・mathlibのhomologyの同型、exactnessの像＝核による成分判定、
  短完全列・単射・全射の成分判定。原論文との対応は[接続記録](docs/rightmodule_homological_bridge.md)。
- 任意のMへの線形Yoneda同型、表現可能加群の射影性と直和による射影提示。
- 正次数の右積のspanとradicalの一致、s_vの対角成分1次元・他の成分零、単純性と短完全列。
- 標準射影分解、実際のExtの存在とk線形性、Ext⁰の線形Yoneda同型と高次Ext(P_i,M)の消滅。
- 一般radical・minimality、有限AS分解からmathlib ProjectiveResolutionへの変換、実際のsyzygy短完全列。
- 具体的ASRegular、実際のExt³(s_(tau v),P_v)≃k、他Ext消滅、数値的AS双対性の順方向と有限台の表。その後、有限性を導いて逆方向も証明済み。
  [原論文・実装・残る証明義務](docs/as_resolution_ext_bridge.md)。
- 有限AS分解からの高次Ext消滅・全次数有限性と数値的同値、具体的左加群・左単純商・Extの左作用、
  Hom/Ext⁰の余極限交換と左側の射影性・EnoughProjectives・Extの存在。
  [前回の左双対接続記録](docs/as_finiteness_left_duality.md)。
- 全次数Extと小さい直和の交換、左右の総空間関手の忠実性とexactness、直和上の行列作用と成分左作用への適合性、左右総空間の有限局所単位による同時固定。
  [今回8単位の接続記録・残る義務](docs/ext_coproduct_exchange.md)。
- 巡回微分の回転不変性と、cut次数1での
  \(\Phi=\sum_{\rho\in C}[\rho\partial_\rho\Phi]\)。
- 正の次数を下げるHilbert漸化式の一意性、およびquadratic型の数値解
  \(h_m=\binom{m+2}{2}\)と二次式による増大上界。
- 本物のテンソル積による(3,3,3)係数表示、cut関係への線形同型、27次元性。
- 三角形箙のcut次数1の閉路が長さ3を持つこと。

次の結果は**条件付きの中間補題**です。

- 正次数成分の分解が与えられた場合の生成の帰納法。
- 任意の有限台次元表についての数値補題。今回、実際のExtから有限台表と非零項を導く順方向も接続済み。
- coherentな有限区間同型が与えられた場合の大域的な周期同型の構成。
- 完全忠実な線形関手と対象同型が与えられた場合の、Homの積を保つ共役。

最小分解d₁からの生成条件・原論文(1.8)/(1.10)・実際の道代数全射は証明済みです。構成した生成元についての核の矢イデアル平方への包含(1.9)と道代数商同型も証明済みです。任意の基底の持上げ・選択の独立性、最小関係と幾何的な共役・tilting・CY completionへの接続は未証明です。数値Ext表とcoherentなWindowSystemおよび正負周期性はASRegularから証明済みです。
詳細は[STATUS.md](STATUS.md)、[GAPS.md](GAPS.md)、[HANDOFF.md](HANDOFF.md)を参照して下さい。

## 再現

Lean `leanprover/lean4:v4.24.0`、mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`を使います。
`lakefile.lean`はタグでなくコミットを指定し、`lake-manifest.json`は全依存コミットを固定します。
Python 3、Git、bash、およびelanか固定Leanの配布物が必要です。

```bash
elan toolchain install leanprover/lean4:v4.24.0
bash scripts/check.sh --prepare-cache
```

キャッシュが揃った後は`bash scripts/check.sh`で検証できます。
`--prepare-cache`は実際にimportするmathlibモジュールとその依存のキャッシュを取得します。
キャッシュ取得自体は本プロジェクトの証明の検証ではありません。
再現のために`lake update`を実行する必要はありません。

今回のCodexクラウド環境では、用意済みの固定配布物を次のように使えます。

```bash
USE_FRO_CACHE=1 AS_GINZBURG_LEAN_ROOT=/workspace/.cloud-setup/lean-4.24.0-linux \
  bash scripts/check.sh --prepare-cache
```

`USE_FRO_CACHE=1`はmathlib公式キャッシュクライアントのCloudflare取得先を選びます。
今回のクラウドではAzure取得先にCONNECT 403があり、許可済みのCloudflare取得先を使用しました。
コマンド実行環境のネットワーク権限と既存プロキシが必要です。
キャッシュは既定で`.lake/cache/mathlib/`に保存し、`MATHLIB_CACHE_DIR`で変更できます。
古い特殊環境向けの`AS_GINZBURG_PROC_SELF_FIX=1`は通常不要で、今回の検証でも使いません。

`check.sh`と`with_lean.sh`にはGitで実行権限を記録し、内部のラッパー呼出しも`bash`経由にしました。
`ASGinzburg.lean`は全数学モジュールをimportします。
`AxiomAudit.lean`は生成された全明示的宣言と名前付きinstanceに`#print axioms`を実行します。
`check.sh`のビルドは数学ライブラリ`ASGinzburg`を指定し、公理監査は後続の独立段階で一度だけ実行します。
`--axiom-jobs 3`等で全宣言監査を分割して同時に実行できます（既定は1）。
各部分の実終了コード・厳密な宣言照合・許容公理・ソースとログSHAを記録し、全件を再照合してから成功を認定します。
自動生成の構成子・射影等はこの明示的宣言件数に含みません。
許容する依存公理は`propext`、`Classical.choice`、`Quot.sound`のみです。
`sorry`、`admit`、独自`axiom`、`sorryAx`、`Lean.ofReduceBool`、`Lean.trustCompiler`を拒否します。
監査一覧・コマンド・ログを重複検査し、現在のソースと一対一で照合します。
161は初期成果の件数であり、将来の宣言追加を制限する固定条件ではありません。

## CIと検証記録

GitHub Actionsの`.github/workflows/lean.yml`はpushとpull_requestで同じ検証コマンドを実行します。
プロセスの終了コードをそのまま失敗に反映し、成功・失敗のどちらでも今回のログをartifactに保存します。
履歴の成功ログをCIの成功判定に使いません。

- `verification/runs/<run-id>/`：毎回新規作成するログ、宣言一覧、環境と検証結果。
- `run.json`：各コマンド・終了コード・UTC開始／終了時刻・単調時計の実測秒・ログSHA-256。
- `verification/latest.json`：最新試行への参照。失敗時も更新。
- `verification/{build.log,axioms.log,declarations.json,results.json}`：最新試行の写し。
- `checkpoints/20261007/verification/`：旧検証記録の無変更保存。旧監査は161コマンド／160異なる名前で、`InWindow.mono`が欠落していました。
- `checkpoints/20261007/{AxiomAudit.lean,preservation.json,recovered_docs/}`：旧監査ソース・保存確認・改訂前の文書。
- `recovery/`と`docs/source.pdf`：過去の回収記録と入力論文。無変更。
- `RECENT_RUN.md`と`runs/`：タスクの目的・差分・実測時間・検査・残ったエラー。
- `AGENTS.md`：継続作業の規約。最新の指示により、自律的に形式化を継続して検証済み単位を直接mainへpushします。

**ビルド成功は実装済み補題の検証を意味します。主定理の完成を意味しません。**

main0076791ff2b0d6c74c05aa2e18ef0a7b871f3467へ検証済み29数学モジュール214〜242と659モジュール全体成功run20261009T082942Z-cddaa6a5を通常fast-forward保存済み。33モジュール243〜275を公開ソースに統合し、現行692モジュールの新しい全体run20261009T092805Z-570508acが進行中。最新の完了した全体検査は659モジュール/3831異なる宣言/2081 theorem、全6段階0、UTC08:29:42.868298→09:14:36.877841、2694.009537847秒。旧成功を現行692モジュールの完了判定に使わない。

証明単位ごとのmainへの保存・Actions・実測時間はRECENT_RUN.md参照。
CLI push認証エラー後は接続済みGitHub APIで検証済みtreeを通常のfast-forward保存。
新規PRなし。数学的ソースの保存確認はverification/ext_sums_preservation.json。

以前のradical-resolutionタスクの最終数学コミットc314180の[main CI](https://github.com/uedakazushi/as-ginzburg-lean/actions/runs/37722129359)はsuccess。
369宣言・177 theoremの監査と12ファイルの当該実行artifact保存を確認。
実行ログと実測時刻はverification/radical_resolution_github_ci.logおよびCI evidence JSONに保存。

前回as-finitenessタスクの最終数学コミット2863bbaの[main CI](https://github.com/uedakazushi/as-ginzburg-lean/actions/runs/37727782672)はsuccess。
505宣言・全223 theoremの新規監査、12ファイルの当該実行artifact保存を確認。
CI検証はUTC 2026-10-08T04:30:31.595999+00:00 → 2026-10-08T04:38:32.459227+00:00、
単調時計で480.863225234秒、終了0。
証拠はverification/as_finiteness_github_ci_evidence.jsonと同名のCI log。
この以前のタスクの終了保存は文書・記録のみ。今回の数学追加の成功判定には、新しい検証と正確なheadのCIを使用する。

前回ext-sumsの数学コミット6666e09の[main CI](https://github.com/uedakazushi/as-ginzburg-lean/actions/runs/37737755500)はsuccess。
636異なる宣言・全274 theoremの新規監査、全7段階終了0、12ファイルのartifact 11532667814保存を確認。
CI検証UTC 2026-10-08T06:28:37.911543+00:00 → 2026-10-08T06:36:04.010329+00:00、単調時計446.098779473秒、終了0。
証拠はverification/ext_sums_github_ci_evidence.jsonと同名のCI log。
この確認後の終了記録の保存は文書・ログのみ。同じ数学ソースを保持し、そのpushも新規CIを開始する。
