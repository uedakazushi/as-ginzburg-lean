# AS有限分解・次元条件の継続形式化

目的：有限AS分解だけから実際のExtの消滅・有限性を導き、命題1.3の数値条件の逆方向へ接続する。
既存RightModule・実際のAbelian.Extを保ち、追加の周期性やExt同型を仮定しない。
定理3.2・系5.2は未証明、形式的な定理文も未実装。

実測開始UTC：2026-10-08T03:32:03+00:00（秒精度のclock観測）。
開始main：a3debe134d372c9b2d47d9fd601a5ea64a332993。
開始時点の同コミットActions 37722967530：success。
AGENTS/HANDOFF/STATUS/GAPS・現行/回収results・最新runを読み、原論文§1.2–1.3を照合済み。
終了時刻・全体経過時間は終了時に実測して記録する。

保存は接続済みGitHub APIで直接main、通常のfast-forward、force=false、新規PRなし。
CLI git pushの前回認証不具合を修復したという主張はしない。

## 単位1：有限AS分解から全ターゲットへの次数4以上のExt消滅

三つの実際のsyzygy短完全列を通る線形dimension shiftを構成した。
最左のrepresentableの射影性から、任意NへのExt(s_w,N,n+4)は全要素零、rank=0。
ASResolutionの存在は原論文(i)の条件であり、総rank=1の(ii)は使っていない。
利用先：有限AS分解からのExt有限性、逆向きの次元条件、有限長双対性。
次：有限coproductのHomとkernelのHomの有限性、低次Extの長完全列による有限性。

初回全体run 20261008T033924Z-3e8fa100はルートimportの配置ミスでbuild終了1。
importを冒頭へ移して新規runで再検証する。失敗ログは削除しない。

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
