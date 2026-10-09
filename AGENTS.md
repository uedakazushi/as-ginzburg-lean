# AS–Ginzburg Lean: 継続作業の規約

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
