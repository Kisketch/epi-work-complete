# Perron / Davis / Komatsu 文献边界核查记录（2026-11-21）
核查对象：paper1_e_plus_pi/00_research_status.md 第 55-62 行文献定位节 5 条声称。类别：第 5 类文献核查与复现。
引用纪律：书目字段只认本次实际打开的原始页面；没打开的一律标未核到。
## 一句总判断
部分核实通过：Davis (1945) 卷期页与题名、Komatsu 2003/2005 卷期页与题名、Komatsu 2009 卷期页均经本次打开的权威页面证实；Perron (1954) 卷一 S33 起始页 p.119（DNB 目录页两次打不开）、Komatsu 2003 定理内页（Thm 1 p.163 / Thm 3 p.166 / Thm 6 p.172）、Komatsu 2005 定理内页（Thm 1-2 p.49 / Thm 3-4 p.50）因付费墙与工具限制未能打开全文，维持未核到；另发现 1 处引用瑕疵（见第 3 节）。
## 逐条对照表（检索日期均为 2026-11-21）
表列：文献 | 声称 | 实测页面结果 | 状态 | 来源 URL + 检索日期。
1. Perron (1954) 卷一 S33：声称 S33 起始于 p.119，目录未载节内 Satz 编号。实测：DNB 目录页打不开（错误原文见下）；检索无佐证；节内 Satz 编号需全文。状态：未核到（需全文、未核实）。来源：https://d-nb.info/453736947/04（2026-11-21，两次 Transport error 未能打开）。
2. Davis (1945)：声称卷期 s1-20/4 与起止页 194-198 已与期刊目录核对。实测：CrossRef 元数据证实题名 On some Simple Continued Fractions Connected with e，卷 s1-20，期 4，页 194-198，印刷出版 1945-10，出版社 Wiley，DOI 10.1112/jlms/s1-20.4.194；Oxford 期刊页 403 打不开。状态：已核实（书目级）；原文精确定理号未核到。来源：https://api.crossref.org/works/10.1112/jlms/s1-20.4.194（已打开）；https://academic.oup.com/jlms/issue/s1-20/4（403 未能打开）。
3. Komatsu 2003 (Acta Arith.)：声称 Thm 1/3 给单双参数 Tasoev 级数式、Thm 6 给 tan 型，页码 Thm 1 p.163 / Thm 3 p.166 / Thm 6 p.172。实测：DOI 着陆页证实 On Hurwitzian and Tasoevs continued fractions, Acta Arith. 107(2), 161-177, DOI 10.4064/aa107-2-4；作者主页第 22 条一致；IMPAN 出版方 PDF 链接有效但本工具不支持解析 PDF。状态：已核实（书目级）；定理内页未核到。来源：https://doi.org/10.4064/aa107-2-4（已打开）；作者主页（已打开，见下）；IMPAN PDF（返回 application/pdf，内容未读）。
4. Komatsu 2005 (Monatshefte)：声称 Thm 1-2 (p.49) 给三周期 e 型 Hurwitz 级数式、Thm 3-4 (p.50) 给 Tasoev 型。实测：Springer 页证实题名 Hurwitz and Tasoev Continued Fractions, Monatsh. Math. 145, 47-60 (2005), DOI 10.1007/s00605-004-0281-0，收稿 2003-10-20，接受 2004-05-12；全文订阅墙；Scribd 转录页仅确认题名与 14 页篇幅，登录墙内全文未读。状态：已核实（书目级）；定理内页未核到。来源：https://link.springer.com/article/10.1007/s00605-004-0281-0（已打开）；Scribd 页（仅题名可读，全文未读）。
5. Komatsu 2009：声称作者主页确认卷 129 pp.358-366。实测：作者主页第 47 条证实 Shrinking the period length of quasi-periodic continued fractions, J. Number Theory 129 (2009), 358-366。状态：已核实（书目级）；全文定理未核。来源：https://sites.google.com/view/takaokomatsu/research/research-papers（2026-11-21 已打开）。
## 打不开页面的错误原文（逐字保留）
甲 DNB：Transport error (GET https://d-nb.info/453736947/04)；基记录 https://d-nb.info/453736947 同错。
乙 Oxford：StatusCode: non 2xx status code (403 GET https://academic.oup.com/jlms/issue/s1-20/4)。
丙 IMPAN PDF：Unsupported fetched file content type: application/pdf（链接有效但本工具读不了 PDF）。
## 引用错误与瑕疵区
瑕疵 1：第 60 行期刊元数据与公开文本转录已交叉核对定理页。Scribd 转录全文在登录墙内，本次仅确认题名与 14 页篇幅，无法以该转录佐证任何定理页码。建议将转录交叉核对降级为未核到，仅保留 Springer 元数据已核实部分。
瑕疵 2（超出核实范围，非证伪）：第 57 行定理内页 p.163/p.166/p.172 与第 58 行 S33 起始于 p.119，本次均未能打开对应全文或目录页，按 AGENTS S3 应标未核到；这不是否定原记录，系本次无法复核。
无证伪项：已打开页面中无任何书目字段与声称矛盾；Davis 卷期页、Komatsu 2003/2005 卷期与题名、Komatsu 2009 卷期页全部一致。
## 全文获取权威途径（建议线索，非已验证结论）
Perron 1954 第 3 版卷一：DNB 记录页恢复后重试；Springer 1977 年重印本；WorldCat 馆际互借。注意 archive.org 现有 1913 年首版扫描（本次验证元数据存在：xii, 520 页，密歇根藏本），但首版与第 3 版节号页码可能不同，不可混用佐证 p.119。Davis 1945 走 Wiley DOI 机构权限。Komatsu 2003 用可读 PDF 的工具打开 IMPAN 出版方 PDF 即补核内页。Komatsu 2005 走 Springer 机构登录或单篇购买。Komatsu 2009 经 JNT 出版商或机构库获取。
## 它没做到什么
1. 未取得任何付费墙内全文，定理级页码维持未核到。2. 只处理书目与页码边界，不涉数学内容正确性，不对 e+π 无理性构成推进。3. DNB 与 Oxford 打不开系本次网络与工具限制，不等于原链接失效，建议主会话换环境复试 DNB 目录页一次。
补记：上文第 3 条中 Tasoevs 系 Tasoev's 之笔误（写入时省略撇号），题名以 DOI 着陆页为准。
