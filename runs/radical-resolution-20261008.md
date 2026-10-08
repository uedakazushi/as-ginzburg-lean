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
