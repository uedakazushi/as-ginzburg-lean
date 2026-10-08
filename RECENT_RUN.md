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
