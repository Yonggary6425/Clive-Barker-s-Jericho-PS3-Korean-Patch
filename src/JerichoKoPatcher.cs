// Clive Barker's Jericho (PS3, BLUS30063) Korean patcher.
// Ships only the Korean translation, subtitles and patch values. Everything derived from the game
// (untranslated text, font tables, re-encoded video) is generated on the user's PC from the user's own files.
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Drawing;
using System.Drawing.Imaging;
using System.Drawing.Text;
using System.IO;
using System.IO.Compression;
using System.Linq;
using System.Net;
using System.Reflection;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading;
using System.Windows.Forms;

static class Core
{
    public const string EnglishSha = "4531f435620a5bfbc7b98d3e2bc23cf81197f22c0a4fb70c7bf24c35a76c7cf1";
    public const string ElfSha = "baa82792fec1b5b3f3324fc895c25ce5fadeabda81fa586f3f95f5c4473f2538";
    public const string PpuHash = "PPU-394a5007acf857dbf3a6ea5151151ea413b9c412";
    public const string PatchFile = "BLUS30063_patch.yml"; // RPCS3 reads <serial>_patch.yml for the running title
    static readonly Encoding L1 = Encoding.GetEncoding(28591);
    public static Action<string> Log = delegate { };

    // value = 32-bit big-endian word written at the virtual address
    static readonly uint[,] FontWords = {
        {0x0047cef0,0x3B800001},{0x0047ca78,0x419EFB84},{0x0047cd00,0x419EFA20},{0x0047ce7c,0x419EFB04},
        {0x0047d570,0x419E00E8},{0x0047b8e4,0x4BFFFE34},{0x00127db0,0x39290005}};
    static readonly uint[,] BonusWords = {{0x0001be48,0x88630000},{0x0001be4c,0x3863FFD0},{0x0001be50,0x7C6307B4},{0x0001be54,0x4E800020}};

    static byte[] Res(string name)
    {
        using (var s = Assembly.GetExecutingAssembly().GetManifestResourceStream(name))
        using (var m = new MemoryStream()) { s.CopyTo(m); return m.ToArray(); }
    }
    static string Sha(byte[] b) { using (var h = SHA256.Create()) return BitConverter.ToString(h.ComputeHash(b)).Replace("-", "").ToLowerInvariant(); }

    // ---------- BFPK ----------
    class Pack
    {
        FileStream f; long start; Dictionary<string, long> off = new Dictionary<string, long>(StringComparer.OrdinalIgnoreCase);
        public Pack(string path, long startOffset)
        {
            f = File.OpenRead(path); start = startOffset; f.Position = start; var r = new BinaryReader(f);
            if (L1.GetString(r.ReadBytes(4)) != "BFPK" || r.ReadUInt32() != 1) throw new Exception("Data00.packed 형식이 다릅니다.");
            uint n = r.ReadUInt32();
            for (uint i = 0; i < n; i++) { int l = r.ReadInt32(); string name = L1.GetString(r.ReadBytes(l)); r.ReadUInt32(); uint o = r.ReadUInt32(); if (!off.ContainsKey(name)) off[name] = o; }
        }
        public byte[] Read(string name)
        {
            long o; if (!off.TryGetValue(name, out o)) throw new Exception("게임 파일에서 찾을 수 없습니다: " + name);
            f.Position = start + o; var r = new BinaryReader(f); int c = r.ReadInt32(); var z = r.ReadBytes(c);
            using (var d = new DeflateStream(new MemoryStream(z, 2, z.Length - 2), CompressionMode.Decompress))
            using (var m = new MemoryStream()) { d.CopyTo(m); return m.ToArray(); }
        }
        public void Close() { f.Close(); }
    }
    static byte[] Zlib(byte[] raw)
    {
        var m = new MemoryStream(); m.WriteByte(0x78); m.WriteByte(0x9C);
        using (var d = new DeflateStream(m, CompressionLevel.Optimal, true)) d.Write(raw, 0, raw.Length);
        uint a = 1, b = 0; foreach (byte x in raw) { a = (a + x) % 65521; b = (b + a) % 65521; }
        uint ad = (b << 16) | a; m.WriteByte((byte)(ad >> 24)); m.WriteByte((byte)(ad >> 16)); m.WriteByte((byte)(ad >> 8)); m.WriteByte((byte)ad);
        return m.ToArray();
    }
    static void WriteModPack(string path, SortedDictionary<string, byte[]> files)
    {
        var names = files.Keys.ToList(); var blobs = new List<byte[]>(); var sizes = new List<int>();
        foreach (var n in names) { var z = Zlib(files[n]); var b = new byte[4 + z.Length]; BitConverter.GetBytes(z.Length).CopyTo(b, 0); z.CopyTo(b, 4); blobs.Add(b); sizes.Add(files[n].Length); }
        int t = 12; foreach (var n in names) t += 4 + n.Length + 8;
        using (var f = File.Create(path + ".tmp"))
        {
            var w = new BinaryWriter(f); w.Write(L1.GetBytes("BFPK")); w.Write(1u); w.Write((uint)names.Count);
            uint o = (uint)t;
            for (int i = 0; i < names.Count; i++) { w.Write(names[i].Length); w.Write(L1.GetBytes(names[i])); w.Write(sizes[i]); w.Write(o); o += (uint)blobs[i].Length; }
            foreach (var b in blobs) w.Write(b);
            w.Write(new byte[0x10000]); w.Flush();
        }
        if (File.Exists(path)) File.Delete(path);
        File.Move(path + ".tmp", path);
    }

    // ---------- font ----------
    class Glyph { public int Cp, X, Y, W, H; }
    static byte[] Dxt5(byte[] a, int W, int H)
    {
        var o = new byte[(W / 4) * (H / 4) * 16]; int p = 0; var px = new int[16]; var pal = new int[8];
        for (int by = 0; by < H; by += 4) for (int bx = 0; bx < W; bx += 4)
            {
                int mn = 255, mx = 0;
                for (int y = 0; y < 4; y++) for (int x = 0; x < 4; x++) { int v = a[(by + y) * W + bx + x]; px[y * 4 + x] = v; if (v < mn) mn = v; if (v > mx) mx = v; }
                o[p] = (byte)mx; o[p + 1] = (byte)mn; ulong bits = 0;
                if (mx != mn)
                {
                    pal[0] = mx; pal[1] = mn; for (int i = 1; i < 7; i++) pal[i + 1] = (int)Math.Floor(((7 - i) * mx + i * mn) / 7.0 + 0.5);
                    for (int i = 0; i < 16; i++) { int best = 0, bd = int.MaxValue; for (int k = 0; k < 8; k++) { int d = Math.Abs(pal[k] - px[i]); if (d < bd) { bd = d; best = k; } } bits |= (ulong)best << (3 * i); }
                }
                for (int i = 0; i < 6; i++) o[p + 2 + i] = (byte)(bits >> (8 * i));
                o[p + 8] = o[p + 9] = o[p + 10] = o[p + 11] = 0xFF; p += 16;
            }
        return o;
    }
    static void BE16(byte[] b, int o, int v) { b[o] = (byte)(v >> 8); b[o + 1] = (byte)v; }
    static void BE32(byte[] b, int o, uint v) { b[o] = (byte)(v >> 24); b[o + 1] = (byte)(v >> 16); b[o + 2] = (byte)(v >> 8); b[o + 3] = (byte)v; }
    static uint RBE32(byte[] b, int o) { return (uint)(b[o] << 24 | b[o + 1] << 16 | b[o + 2] << 8 | b[o + 3]); }
    static void LE32(byte[] b, int o, uint v) { BitConverter.GetBytes(v).CopyTo(b, o); }

    static HashSet<char> BuildFont(IEnumerable<string> texts, SortedDictionary<string, byte[]> outp)
    {
        const int W = 4096, H = 2048, CellH = 60, Pad = 2; const float Px = 48;
        var set = new SortedSet<char>(); var euc = Encoding.GetEncoding(51949);
        for (int hi = 0xb0; hi <= 0xc8; hi++) for (int lo = 0xa1; lo <= 0xfe; lo++) foreach (char c in euc.GetString(new[] { (byte)hi, (byte)lo })) set.Add(c);
        foreach (char c in "…·‘’“”–—~!?、。「」『』《》〈〉※★☆○●◎◇◆□■△▲▽▼→←↑↓") set.Add(c);
        foreach (var t in texts) foreach (char c in t) set.Add(c);
        var chars = set.Where(c => c > 0xff && !char.IsSurrogate(c)).ToList();
        var fam = new InstalledFontCollection().Families.Any(f => f.Name == "Malgun Gothic" || f.Name == "맑은 고딕");
        if (!fam) throw new Exception("맑은 고딕 글꼴을 찾을 수 없습니다.");
        var glyphs = new List<Glyph>(); var alpha = new byte[W * H];
        using (var bmp = new Bitmap(W, H, System.Drawing.Imaging.PixelFormat.Format32bppArgb))
        using (var g = Graphics.FromImage(bmp))
        using (var font = new Font("Malgun Gothic", Px, FontStyle.Bold, GraphicsUnit.Pixel))
        {
            g.Clear(Color.Black); g.TextRenderingHint = TextRenderingHint.AntiAliasGridFit;
            var fmt = new StringFormat(StringFormat.GenericTypographic); fmt.FormatFlags |= StringFormatFlags.MeasureTrailingSpaces;
            int x = 1, y = 1;
            foreach (char ch in chars)
            {
                string s = ch.ToString(); var sz = g.MeasureString(s, font, 1000, fmt);
                int w = (int)Math.Ceiling(sz.Width) + 2; if (w < 6) w = (int)(Px / 3);
                if (x + w + 1 >= W) { x = 1; y += CellH + 2; }
                if (y + CellH >= H) throw new Exception("글꼴 이미지 공간이 부족합니다.");
                g.DrawString(s, font, Brushes.White, (float)(x + 1), (float)(y + (CellH - font.Height) / 2.0), fmt);
                glyphs.Add(new Glyph { Cp = ch, X = x, Y = y, W = w, H = CellH }); x += w + 2;
            }
            g.Flush();
            var d = bmp.LockBits(new Rectangle(0, 0, W, H), ImageLockMode.ReadOnly, bmp.PixelFormat);
            var raw = new byte[W * H * 4]; Marshal.Copy(d.Scan0, raw, 0, raw.Length); bmp.UnlockBits(d);
            for (int i = 0; i < W * H; i++) alpha[i] = raw[i * 4 + 1];
        }
        foreach (var gl in glyphs)
        {
            int mn = int.MaxValue, mx = -1;
            for (int xx = gl.X; xx < gl.X + gl.W; xx++) for (int yy = gl.Y; yy < gl.Y + gl.H; yy++) if (alpha[yy * W + xx] > 24) { if (xx < mn) mn = xx; if (xx > mx) mx = xx; break; }
            if (mx < 0) continue;
            int nx = Math.Max(gl.X - 1, mn - Pad), nr = Math.Min(gl.X + gl.W + 1, mx + 1 + Pad); gl.X = nx; gl.W = nr - nx;
        }
        var levels = new List<byte[]>(); var cur = alpha; int lw = W, lh = H;
        while (true)
        {
            levels.Add(Dxt5(cur, lw, lh)); if (lw <= 4 || lh <= 4) break;
            int nw = lw / 2, nh = lh / 2; var nb = new byte[nw * nh];
            for (int y = 0; y < nh; y++) for (int x = 0; x < nw; x++) nb[y * nw + x] = (byte)((cur[2 * y * lw + 2 * x] + cur[2 * y * lw + 2 * x + 1] + cur[(2 * y + 1) * lw + 2 * x] + cur[(2 * y + 1) * lw + 2 * x + 1] + 2) >> 2);
            cur = nb; lw = nw; lh = nh;
        }
        var hdr = new byte[128]; L1.GetBytes("DDS ").CopyTo(hdr, 0); LE32(hdr, 4, 124); LE32(hdr, 8, 0x0a1007); LE32(hdr, 12, H); LE32(hdr, 16, W); LE32(hdr, 20, W * H); LE32(hdr, 28, (uint)levels.Count);
        LE32(hdr, 76, 32); LE32(hdr, 80, 4); L1.GetBytes("DXT5").CopyTo(hdr, 84); LE32(hdr, 108, 0x401008);
        var dds = new MemoryStream(); dds.Write(hdr, 0, 128); foreach (var l in levels) dds.Write(l, 0, l.Length);
        outp["2d/fonts/dds/unicode.alpha.dds"] = dds.ToArray();
        int n = glyphs.Count + 1; var m = new byte[0x18 + n * 8];
        L1.GetBytes("MST\0").CopyTo(m, 0); BE32(m, 4, (uint)m.Length - 8); BE32(m, 8, 100); BE32(m, 12, W); BE32(m, 16, H); BE32(m, 20, (uint)n);
        for (int i = 0; i < glyphs.Count; i++) { int p = 0x18 + (i + 1) * 8; var q = glyphs[i]; BE16(m, p, q.X); BE16(m, p + 2, q.Y); BE16(m, p + 4, q.W); BE16(m, p + 6, q.H); }
        outp["2d/fonts/unicode.alpha.mstb"] = m;
        int first = glyphs.Min(q => q.Cp), last = glyphs.Max(q => q.Cp); var u = new byte[4 + (last - first + 1) * 2];
        BE16(u, 0, first); BE16(u, 2, last); for (int i = 0; i < glyphs.Count; i++) BE16(u, 4 + (glyphs[i].Cp - first) * 2, i + 1);
        outp["2d/fonts/unicode.alpha.uct"] = u;
        Log("글꼴 생성: " + glyphs.Count + "자");
        return new HashSet<char>(chars);
    }

    // ---------- install ----------
    public static string UsrDir(string game)
    {
        foreach (var c in new[] { Path.Combine(game, "PS3_GAME", "USRDIR"), Path.Combine(game, "USRDIR"), game })
            if (File.Exists(Path.Combine(c, "Data00.packed"))) return c;
        throw new Exception("게임 폴더에서 PS3_GAME\\USRDIR\\Data00.packed 를 찾을 수 없습니다.");
    }
    static Dictionary<string, string> LoadKo()
    {
        var d = new Dictionary<string, string>(); byte[] raw;
        using (var g = new GZipStream(new MemoryStream(Res("ko.tsv.gz")), CompressionMode.Decompress)) using (var m = new MemoryStream()) { g.CopyTo(m); raw = m.ToArray(); }
        foreach (var l in Encoding.UTF8.GetString(raw).Split('\n')) { int i = l.IndexOf('\t'); if (i > 0) d[l.Substring(0, i)] = l.Substring(i + 1); }
        return d;
    }
    public static void InstallText(string usr) { InstallText(usr, Path.Combine(usr, "Data00.packed"), 0); }
    // dataOffset: where Data00.packed starts inside dataPath (non-zero when reading straight from an ISO)
    public static void InstallText(string usr, string dataPath, long dataOffset)
    {
        Log("게임 파일 확인 중...");
        var pack = new Pack(dataPath, dataOffset);
        var outp = new SortedDictionary<string, byte[]>(StringComparer.Ordinal);
        try
        {
            var en = pack.Read("language/english.txt");
            if (Sha(en) != EnglishSha) throw new Exception("이 Data00.packed는 지원하는 원본(BLUS30063 v1.01)이 아니거나 이미 수정된 파일입니다.");
            var ko = LoadKo();
            var have = BuildFont(ko.Values, outp);
            var sub = new Dictionary<char, string> { { '…', "..." }, { '‘', "'" }, { '’', "'" }, { '“', "\"" }, { '”', "\"" }, { '–', "-" }, { '—', "-" } };
            var sb = new StringBuilder(); int used = 0;
            foreach (var line in L1.GetString(en).Split(new[] { "\r\n" }, StringSplitOptions.None))
            {
                if (sb.Length > 0 || used > 0) sb.Append("\r\n"); used++;
                int i = line.IndexOf('\t'); string val;
                if (i > 0 && ko.TryGetValue(line.Substring(0, i), out val))
                {
                    sb.Append(line, 0, i + 1);
                    foreach (char c in val) { string s; if (c <= 0xff) sb.Append(c); else if (have.Contains(c)) sb.Append('\x01').Append(((int)c).ToString("X4")); else if (sub.TryGetValue(c, out s)) sb.Append(s); else sb.Append('?'); }
                }
                else sb.Append(line);
            }
            outp["language/english.txt"] = L1.GetBytes(sb.ToString());
            var fnt = L1.GetString(pack.Read("2d/fonts/fonts.fnt"));
            outp["2d/fonts/fonts.fnt"] = L1.GetBytes(Regex.Replace(fnt, @"^first = 1(?=\r?$)", "first = 2", RegexOptions.Multiline));
            foreach (var n in new[] { "ps3manson60", "ps3adler37", "ps3arial20" })
            {
                var m = pack.Read("2d/fonts/" + n + ".alpha.mstb"); var o = new byte[m.Length - 8];
                Array.Copy(m, 0, o, 0, 0x20); Array.Copy(m, 0x28, o, 0x20, m.Length - 0x28);
                BE32(o, 20, RBE32(m, 20) - 1); BE32(o, 4, (uint)o.Length - 8); outp["2d/fonts/" + n + ".alpha.mstb"] = o;
            }
        }
        finally { pack.Close(); }
        var mods = Path.Combine(usr, "mods"); Directory.CreateDirectory(mods);
        WriteModPack(Path.Combine(mods, "korean.packed"), outp);
        Log("한글 데이터 설치 완료: mods\\korean.packed");
    }
    static string Yaml(string desc, string notes, uint[,] w)
    {
        var s = new StringBuilder("  \"" + desc + "\":\n    Games:\n      \"Clive Barker's Jericho\":\n        BLUS30063: [ All ]\n    Author: \"Jericho KO patch\"\n    Notes: \"" + notes + "\"\n    Patch Version: 1.0\n    Patch:\n");
        for (int i = 0; i < w.GetLength(0); i++) s.AppendFormat("      - [ be32, 0x{0:x8}, 0x{1:X8} ]\n", w[i, 0], w[i, 1]);
        return s.ToString();
    }
    public static void InstallRpcs3(string dir)
    {
        if (!File.Exists(Path.Combine(dir, "rpcs3.exe")) && !Directory.Exists(Path.Combine(dir, "config"))) throw new Exception("RPCS3 폴더가 아닙니다: " + dir);
        var pd = Path.Combine(dir, "patches"); Directory.CreateDirectory(pd);
        string y = "Version: 1.2\n\n" + PpuHash + ":\n" + Yaml("Korean font fixes", "Korean glyph rendering fixes", FontWords) + Yaml("Bonus codes: enter 1-9", "Enter one digit 1-9 on the Bonus Codes screen", BonusWords);
        var pf = Path.Combine(pd, PatchFile); string prev = File.Exists(pf) ? File.ReadAllText(pf) : "";
        if (prev.Contains(PpuHash + ":")) Log("주의: " + PatchFile + "에 이 게임 항목이 이미 있어 그대로 두었습니다.");
        else if (prev.Length > 0) { File.Copy(pf, pf + ".jericho_ko.bak", true); if (!prev.EndsWith("\n")) prev += "\n"; File.WriteAllText(pf, prev + "\n" + y.Substring(y.IndexOf(PpuHash)), new UTF8Encoding(false)); }
        else File.WriteAllText(pf, y, new UTF8Encoding(false));
        var cd = Path.Combine(dir, "config"); Directory.CreateDirectory(cd); var cf = Path.Combine(cd, "patch_config.yml");
        string old = File.Exists(cf) ? File.ReadAllText(cf) : "";
        if (old.Contains(PpuHash + ":")) { Log("주의: patch_config.yml에 이 게임 항목이 이미 있어 그대로 두었습니다. RPCS3의 관리 > 게임 패치에서 켜 주세요."); return; }
        if (old.Length > 0) { File.Copy(cf, cf + ".jericho_ko.bak", true); if (!old.EndsWith("\n")) old += "\n"; }
        Func<string, string> en = d => "  \"" + d + "\":\n    \"Clive Barker's Jericho\":\n      BLUS30063:\n        All:\n          Enabled: true\n";
        File.WriteAllText(cf, old + PpuHash + ":\n" + en("Korean font fixes") + en("Bonus codes: enter 1-9"), new UTF8Encoding(false));
        Log("RPCS3 게임 패치 설치 및 활성화 완료");
    }

    // ---------- video ----------
    class Bink
    {
        public byte[] B; public uint Frames, W, H, N, FpsN, FpsD, VFlags; public int[] Off; public int AudioHdr;
        public Bink(string p) : this(File.ReadAllBytes(p)) { }
        public Bink(byte[] data)
        {
            B = data; Frames = U(8); W = U(20); H = U(24); FpsN = U(28); FpsD = U(32); VFlags = U(36); N = U(40);
            AudioHdr = 44; int o = 44 + (int)N * 12; Off = new int[Frames + 1]; for (int i = 0; i <= Frames; i++) Off[i] = (int)U(o + i * 4);
        }
        public uint U(int o) { return BitConverter.ToUInt32(B, o); }
        public void Frame(int i, out int vStart, out int end, out int start) { start = Off[i] & ~1; end = Off[i + 1] & ~1; int p = start; for (int t = 0; t < N; t++) p += 4 + (int)U(p); vStart = p; }
        public long VideoBytes() { long s = 0; for (int i = 0; i < Frames; i++) { int v, e, st; Frame(i, out v, out e, out st); s += e - v; } return s; }
    }
    static void Remux(Bink o, Bink v, string path)
    {
        if (o.Frames != v.Frames || v.N != 0 || o.W != v.W || o.H != v.H) throw new Exception("영상 프레임 정보가 맞지 않습니다.");
        int n = (int)o.N, F = (int)o.Frames, hl = 44 + 12 * n + 4 * (F + 1); uint pos = (uint)hl, maxF = 0; var offs = new uint[F + 1];
        for (int i = 0; i < F; i++) { int ov, oe, os, vv, ve, vs; o.Frame(i, out ov, out oe, out os); v.Frame(i, out vv, out ve, out vs); uint len = (uint)((ov - os) + (ve - vv)); offs[i] = pos | (uint)(v.Off[i] & 1); pos += len; if (len > maxF) maxF = len; }
        offs[F] = pos; var h = new byte[hl]; Array.Copy(o.B, 0, h, 0, 4); LE32(h, 4, pos - 8); LE32(h, 8, (uint)F); LE32(h, 12, maxF); LE32(h, 16, (uint)F); LE32(h, 20, o.W); LE32(h, 24, o.H); LE32(h, 28, o.FpsN); LE32(h, 32, o.FpsD); LE32(h, 36, v.VFlags); LE32(h, 40, (uint)n);
        Array.Copy(o.B, 44, h, 44, 12 * n); for (int i = 0; i <= F; i++) LE32(h, 44 + 12 * n + i * 4, offs[i]);
        using (var f = new FileStream(path, FileMode.Create, FileAccess.Write, FileShare.None, 1 << 20))
        {
            f.Write(h, 0, hl);
            for (int i = 0; i < F; i++) { int ov, oe, os, vv, ve, vs; o.Frame(i, out ov, out oe, out os); v.Frame(i, out vv, out ve, out vs); f.Write(o.B, os, ov - os); f.Write(v.B, vv, ve - vv); }
        }
    }
    static void Run(string exe, string args, string cwd)
    {
        var p = new ProcessStartInfo(exe, args) { UseShellExecute = false, CreateNoWindow = true, WorkingDirectory = cwd, RedirectStandardError = true, RedirectStandardOutput = true };
        using (var x = Process.Start(p))
        {
            var err = new StringBuilder(); x.ErrorDataReceived += (s, e) => { if (e.Data != null && err.Length < 4000) err.AppendLine(e.Data); }; x.OutputDataReceived += (s, e) => { };
            x.BeginErrorReadLine(); x.BeginOutputReadLine(); x.WaitForExit();
            if (x.ExitCode != 0) throw new Exception(Path.GetFileName(exe) + " 오류 (" + x.ExitCode + "): " + err);
        }
    }
    // Joins the credit screen onto the front of Prologue.bik, the movie the game plays at boot after
    // the logos (Intro.bik plays later). The embedded clip holds track 0 stereo and track 1 mono
    // silence, and every movie track gets the one matching its format, so the movie's audio stays in
    // sync. No encoder is needed, so this works without the subtitle option.
    public static void AddSplash(string usr)
    {
        string cur = Path.Combine(usr, "Video", "Prologue.bik"), bak = cur + ".orig", nb = cur + ".new";
        if (!File.Exists(cur)) throw new Exception("영상을 찾을 수 없습니다: " + cur);
        byte[] raw; using (var g = new GZipStream(new MemoryStream(Res("splash.bik.gz")), CompressionMode.Decompress)) using (var m = new MemoryStream()) { g.CopyTo(m); raw = m.ToArray(); }
        Bink s = new Bink(raw), o = new Bink(cur);
        if (s.W != o.W || s.H != o.H) throw new Exception("영상 크기가 맞지 않습니다.");
        // Compare a mid-clip frame: the clip and a movie can both start on an identical black frame.
        int sv, se, ss, ov, oe, os, mid = (int)s.Frames / 2; s.Frame(mid, out sv, out se, out ss); o.Frame(mid, out ov, out oe, out os);
        if (se - sv == oe - ov) { bool same = true; for (int i = 0; i < se - sv && same; i++) same = s.B[sv + i] == o.B[ov + i]; if (same) { Log("제작자 화면: 이미 들어 있습니다."); return; } }
        int n = (int)o.N, SF = (int)s.Frames, OF = (int)o.Frames, F = SF + OF, hl = 44 + 12 * n + 4 * (F + 1);
        var src = new int[n]; for (int t = 0; t < n; t++) src[t] = (BitConverter.ToUInt16(o.B, 44 + 4 * n + 4 * t + 2) & 0x2000) != 0 ? 0 : 1;
        Func<int, int[]> packets = i => { int p = s.Off[i] & ~1; int l0 = 4 + (int)s.U(p), l1 = 4 + (int)s.U(p + l0); return new[] { p, l0, p + l0, l1 }; };
        var h = new byte[hl]; Array.Copy(o.B, 0, h, 0, 44 + 12 * n); LE32(h, 8, (uint)F); LE32(h, 16, (uint)F);
        uint pos = (uint)hl, maxF = 0; var lens = new uint[SF];
        for (int i = 0; i < SF; i++)
        {
            var a = packets(i); int v, e, st; s.Frame(i, out v, out e, out st); uint len = (uint)(e - v); foreach (int t in src) len += (uint)a[1 + 2 * t];
            LE32(h, 44 + 12 * n + i * 4, pos | (uint)(s.Off[i] & 1)); pos += len; lens[i] = len; if (len > maxF) maxF = len;
        }
        for (int i = 0; i < OF; i++)
        {
            uint len = (uint)((o.Off[i + 1] & ~1) - (o.Off[i] & ~1));
            LE32(h, 44 + 12 * n + (SF + i) * 4, pos | (uint)(o.Off[i] & 1)); pos += len; if (len > maxF) maxF = len;
        }
        LE32(h, 44 + 12 * n + F * 4, pos); LE32(h, 4, pos - 8); LE32(h, 12, maxF);
        using (var f = new FileStream(nb, FileMode.Create, FileAccess.Write, FileShare.None, 1 << 20))
        {
            f.Write(h, 0, hl);
            for (int i = 0; i < SF; i++)
            {
                var a = packets(i); foreach (int t in src) f.Write(s.B, a[2 * t], a[1 + 2 * t]);
                int v, e, st; s.Frame(i, out v, out e, out st); f.Write(s.B, v, e - v);
            }
            int first = o.Off[0] & ~1; f.Write(o.B, first, (o.Off[OF] & ~1) - first);
        }
        if (!File.Exists(bak)) File.Move(cur, bak); else File.Delete(cur);
        File.Move(nb, cur); Log("제작자 화면을 오프닝 앞에 넣었습니다.");
    }
    public static void InstallVideo(string usr, string ffmpeg, string rad)
    {
        foreach (var v in new[] { new[] { "Intro", "intro_ko.ass" }, new[] { "Prologue", "prologue_ko.ass" } })
        {
            string dir = Path.Combine(usr, "Video"), cur = Path.Combine(dir, v[0] + ".bik"), bak = cur + ".orig", src = File.Exists(bak) ? bak : cur;
            if (!File.Exists(src)) throw new Exception("영상을 찾을 수 없습니다: " + src);
            string tmp = Path.Combine(Path.GetTempPath(), "JerichoKO_" + Guid.NewGuid().ToString("N")); Directory.CreateDirectory(Path.Combine(tmp, "f"));
            try
            {
                File.WriteAllBytes(Path.Combine(tmp, "s.ass"), Res(v[1]));
                Log(v[0] + ": 자막 합성 중 (몇 분 걸립니다)...");
                Run(ffmpeg, "-v error -y -i \"" + src + "\" -an -fps_mode passthrough -vf subtitles=s.ass -compression_level 1 f/f%04d.png", tmp);
                var orig = new Bink(src); int cnt = Directory.GetFiles(Path.Combine(tmp, "f"), "f*.png").Length;
                if (cnt != orig.Frames) throw new Exception("프레임 수가 맞지 않습니다: " + cnt);
                long rate = (long)(orig.VideoBytes() * (double)orig.FpsN / orig.FpsD / orig.Frames);
                Log(v[0] + ": Bink 인코딩 중...");
                Run(rad, "Bink \"" + Path.Combine(tmp, "f", "f????.png") + "*1-" + cnt + "\" \"" + Path.Combine(tmp, "v.bik") + "\" /Bink1 /F29.97 /DataRate" + rate + " /NoSound /O /#", tmp);
                if (!File.Exists(Path.Combine(tmp, "v.bik"))) throw new Exception("Bink 인코딩 결과가 없습니다.");
                var nb = cur + ".new"; Remux(orig, new Bink(Path.Combine(tmp, "v.bik")), nb);
                if (!File.Exists(bak)) File.Move(cur, bak); else File.Delete(cur);
                File.Move(nb, cur); Log(v[0] + ": 완료");
            }
            finally { try { Directory.Delete(tmp, true); } catch { } }
        }
    }
    public static void PatchElf(string path)
    {
        var b = File.ReadAllBytes(path); if (Sha(b) != ElfSha) throw new Exception("지원하는 복호화 EBOOT가 아닙니다 (SHA-256 불일치).");
        Action<uint[,]> ap = w => { for (int i = 0; i < w.GetLength(0); i++) { uint va = w[i, 0]; long phoff = (long)RBE64(b, 0x20); int n = b[0x38] << 8 | b[0x39]; bool ok = false; for (int k = 0; k < n && !ok; k++) { int o = (int)phoff + k * 0x38; ulong off = RBE64(b, o + 8), v = RBE64(b, o + 16), sz = RBE64(b, o + 32); if (RBE32(b, o) == 1 && va >= v && va < v + sz) { BE32(b, (int)(va - v + off), w[i, 1]); ok = true; } } if (!ok) throw new Exception("주소 오류"); } };
        ap(FontWords); ap(BonusWords);
        var o2 = Path.Combine(Path.GetDirectoryName(path), Path.GetFileNameWithoutExtension(path) + "_KO_patched.elf"); File.WriteAllBytes(o2, b); Log("저장: " + o2);
    }
    static ulong RBE64(byte[] b, int o) { return ((ulong)RBE32(b, o) << 32) | RBE32(b, o + 4); }
    public static void Uninstall(string usr, string rpcs3)
    {
        if (usr != null) // null: ISO mode, where only the RPCS3 patch entry is on this PC
        {
            var f = Path.Combine(usr, "mods", "korean.packed"); if (File.Exists(f)) File.Delete(f);
            var m = Path.Combine(usr, "mods"); if (Directory.Exists(m) && !Directory.EnumerateFileSystemEntries(m).Any()) Directory.Delete(m);
            foreach (var v in new[] { "Intro", "Prologue" }) { string c = Path.Combine(usr, "Video", v + ".bik"), b = c + ".orig"; if (File.Exists(b)) { if (File.Exists(c)) File.Delete(c); File.Move(b, c); } }
        }
        if (!string.IsNullOrEmpty(rpcs3)) { var p = Path.Combine(rpcs3, "patches", PatchFile); if (File.Exists(p)) { var t = File.ReadAllText(p); if (t.StartsWith("Version: 1.2\n\n" + PpuHash) && Regex.Matches(t, "^PPU-", RegexOptions.Multiline).Count == 1) File.Delete(p); else Log("주의: " + PatchFile + "에 다른 게임 패치가 있어 지우지 않았습니다."); } }
        Log(usr == null ? "RPCS3 패치를 지웠습니다. 한글 ISO는 파일을 지우면 됩니다." : "되돌리기 완료");
    }

    // ---------- ISO ----------
    public static bool IsIso(string p) { return !string.IsNullOrEmpty(p) && p.EndsWith(".iso", StringComparison.OrdinalIgnoreCase) && File.Exists(p); }
    // A real PS3 only runs SELF files ("SCE\0"); a plain ELF would produce a disc that cannot boot.
    static void RequireSelf(string path)
    {
        if (!File.Exists(path)) throw new Exception("재서명 EBOOT 파일을 찾을 수 없습니다: " + path);
        var head = new byte[4]; using (var s = File.OpenRead(path)) s.Read(head, 0, 4);
        if (head[0] == 0x7F && head[1] == (byte)'E') throw new Exception("이 파일은 재서명 전의 ELF입니다. 재서명 도구로 변환한 EBOOT.BIN을 지정해 주세요.");
        if (!(head[0] == (byte)'S' && head[1] == (byte)'C' && head[2] == (byte)'E' && head[3] == 0)) throw new Exception("서명된 PS3 실행 파일(SELF)이 아닙니다: " + path);
    }
    // signedEboot: optional re-signed EBOOT.BIN that replaces the original on the disc image (null keeps the original)
    public static string InstallIso(string isoPath, Action<string> video, string signedEboot)
    {
        if (signedEboot != null) RequireSelf(signedEboot);
        using (var iso = new Iso(isoPath))
        {
            var usr = iso.Find("PS3_GAME/USRDIR"); var data = iso.Find("PS3_GAME/USRDIR/Data00.packed");
            if (usr == null || data == null) throw new Exception("ISO에서 PS3_GAME\\USRDIR\\Data00.packed 를 찾을 수 없습니다.");
            if (signedEboot != null)
            {
                var eb = iso.Find("PS3_GAME/USRDIR/EBOOT.BIN"); if (eb == null) throw new Exception("ISO에서 EBOOT.BIN을 찾을 수 없습니다.");
                eb.Src = signedEboot; eb.Size = new FileInfo(signedEboot).Length; Log("재서명 EBOOT를 ISO에 넣습니다: " + signedEboot);
            }
            if (iso.Find("PS3_GAME/USRDIR/mods/korean.packed") != null) throw new Exception("이미 한글 패치가 적용된 ISO입니다. 원본 ISO를 지정해 주세요.");
            string output = Path.Combine(Path.GetDirectoryName(Path.GetFullPath(isoPath)), Path.GetFileNameWithoutExtension(isoPath) + "_KOR.iso");
            long need = new FileInfo(isoPath).Length + (200L << 20), free = new DriveInfo(Path.GetPathRoot(Path.GetFullPath(output))).AvailableFreeSpace;
            if (free < need) throw new Exception("저장 공간이 부족합니다. " + (need >> 30) + "GB 이상의 여유 공간이 필요합니다.");
            string work = Path.Combine(Path.GetTempPath(), "JerichoKO_iso_" + Guid.NewGuid().ToString("N")); Directory.CreateDirectory(work);
            try
            {
                InstallText(work, isoPath, data.Lba * Iso.S);
                var modsDir = new Iso.Node { Name = "mods", Dir = true };
                modsDir.Kids.Add(new Iso.Node { Name = "korean.packed", Src = Path.Combine(work, "mods", "korean.packed"), Size = new FileInfo(Path.Combine(work, "mods", "korean.packed")).Length });
                usr.Kids.RemoveAll(k => k.Name.Equals("mods", StringComparison.OrdinalIgnoreCase)); usr.Kids.Add(modsDir);
                Directory.CreateDirectory(Path.Combine(work, "Video")); var names = video != null ? new[] { "Intro", "Prologue" } : new[] { "Prologue" };
                foreach (var v in names)
                {
                    var n = iso.Find("PS3_GAME/USRDIR/Video/" + v + ".bik"); if (n == null) throw new Exception("ISO에서 영상을 찾을 수 없습니다: " + v);
                    Log(v + ": ISO에서 꺼내는 중...");
                    using (var o = File.Create(Path.Combine(work, "Video", v + ".bik"))) iso.Copy(n, o);
                }
                if (video != null) video(work);
                AddSplash(work);
                foreach (var v in names) { var n = iso.Find("PS3_GAME/USRDIR/Video/" + v + ".bik"); n.Src = Path.Combine(work, "Video", v + ".bik"); n.Size = new FileInfo(n.Src).Length; }
                Log("한글 ISO 만드는 중 (몇 분 걸립니다)...");
                iso.Write(output + ".tmp");
            }
            finally { try { Directory.Delete(work, true); } catch { } }
            if (File.Exists(output)) File.Delete(output);
            File.Move(output + ".tmp", output);
            Log("한글 ISO 완성: " + output);
            return output;
        }
    }
}

// Reads a PS3 disc image through its Joliet tree and writes a new image from that tree.
class Iso : IDisposable
{
    public const int S = 2048;
    public class Node { public string Name, Src; public bool Dir; public long Lba, Size; public List<Node> Kids = new List<Node>(); }
    class Entry { public Node N; public Entry Parent; public byte[] Name; public int Index; public List<Node> Sorted; public long Lba, Size; }
    FileStream f; Node root; byte[] s1, pvd, svd, term;
    byte[] Sector(long lba, int len) { f.Position = lba * S; var b = new byte[len]; int got = 0, n; while (got < len && (n = f.Read(b, got, len - got)) > 0) got += n; if (got != len) throw new Exception("ISO 파일이 손상되었거나 잘렸습니다."); return b; }
    public Iso(string path)
    {
        f = File.OpenRead(path);
        if (f.Length < 32 * S) throw new Exception("PS3 ISO 파일이 아닙니다.");
        s1 = Sector(1, S); pvd = Sector(16, S); svd = Sector(17, S); term = Sector(18, S);
        if (Encoding.ASCII.GetString(s1, 0, 12) != "PlayStation3" || pvd[0] != 1 || svd[0] != 2 || term[0] != 255) throw new Exception("지원하는 PS3 ISO 형식이 아닙니다.");
        root = new Node { Name = "", Dir = true, Lba = BitConverter.ToUInt32(svd, 158), Size = BitConverter.ToUInt32(svd, 166) };
        Read(root);
    }
    void Read(Node d)
    {
        var b = Sector(d.Lba, (int)d.Size); int o = 0;
        Node open = null; // a file recorded as several consecutive extents
        while (o < b.Length)
        {
            int len = b[o]; if (len == 0) { o = (o / S + 1) * S; continue; }
            int nl = b[o + 32]; int flags = b[o + 25];
            if (!(nl == 1 && b[o + 33] <= 1))
            {
                string name = Encoding.BigEndianUnicode.GetString(b, o + 33, nl); int semi = name.LastIndexOf(';'); if (semi > 0) name = name.Substring(0, semi);
                var n = new Node { Name = name, Dir = (flags & 2) != 0, Lba = BitConverter.ToUInt32(b, o + 2), Size = BitConverter.ToUInt32(b, o + 10) };
                if (open != null)
                {
                    if (open.Name != n.Name || open.Size % S != 0 || open.Lba + open.Size / S != n.Lba) throw new Exception("연속되지 않은 파일 조각이 있는 ISO는 지원하지 않습니다.");
                    open.Size += n.Size;
                    if (open.Size > uint.MaxValue) throw new Exception("4GB가 넘는 파일이 있는 ISO는 지원하지 않습니다.");
                    if ((flags & 0x80) == 0) open = null;
                }
                else
                {
                    d.Kids.Add(n); if ((flags & 0x80) != 0) open = n;
                    if (n.Dir) Read(n);
                }
            }
            o += len;
        }
    }
    public Node Find(string path)
    {
        var c = root;
        foreach (var part in path.Split('/')) { if (c == null) return null; c = c.Kids.FirstOrDefault(k => k.Name.Equals(part, StringComparison.OrdinalIgnoreCase)); }
        return c;
    }
    public void Copy(Node n, Stream o) { CopyRange(f, n.Lba * S, n.Size, o); }
    static void CopyRange(Stream s, long pos, long size, Stream o)
    {
        s.Position = pos; var buf = new byte[1 << 20]; long left = size;
        while (left > 0) { int n = s.Read(buf, 0, (int)Math.Min(left, buf.Length)); if (n <= 0) throw new Exception("파일을 끝까지 읽지 못했습니다."); o.Write(buf, 0, n); left -= n; }
    }
    static long Align(long n) { return (n + S - 1) / S; }
    static byte[] Enc(Node n, bool joliet)
    {
        string s = (joliet ? n.Name : n.Name.ToUpperInvariant()) + (n.Dir ? "" : ";1");
        return joliet ? Encoding.BigEndianUnicode.GetBytes(s) : Encoding.GetEncoding(28591).GetBytes(s);
    }
    static int Cmp(byte[] a, byte[] b) { for (int i = 0; i < a.Length && i < b.Length; i++) if (a[i] != b[i]) return a[i] - b[i]; return a.Length - b.Length; }
    static List<Entry> Tree(Node top, bool joliet)
    {
        var list = new List<Entry>(); var first = new Entry { N = top, Name = new byte[] { 0 } }; list.Add(first);
        for (int i = 0; i < list.Count; i++)
        {
            var c = list[i]; c.Index = i + 1; c.Sorted = c.N.Kids.ToList(); c.Sorted.Sort((x, y) => Cmp(Enc(x, joliet), Enc(y, joliet)));
            foreach (var k in c.Sorted) if (k.Dir) list.Add(new Entry { N = k, Parent = c, Name = Enc(k, joliet) });
            long used = 68;
            foreach (var k in c.Sorted) { int nl = Enc(k, joliet).Length, l = 33 + nl + (nl % 2 == 0 ? 1 : 0); if (used % S + l > S) used += S - used % S; used += l; }
            c.Size = Align(used) * S;
        }
        return list;
    }
    static void Both32(byte[] b, int o, uint v) { BitConverter.GetBytes(v).CopyTo(b, o); b[o + 4] = (byte)(v >> 24); b[o + 5] = (byte)(v >> 16); b[o + 6] = (byte)(v >> 8); b[o + 7] = (byte)v; }
    static void Be32(byte[] b, int o, uint v) { b[o] = (byte)(v >> 24); b[o + 1] = (byte)(v >> 16); b[o + 2] = (byte)(v >> 8); b[o + 3] = (byte)v; }
    static readonly byte[] Date = { 107, 8, 24, 0, 0, 0, 0 };
    static byte[] Rec(long lba, long size, int flags, byte[] name)
    {
        var b = new byte[33 + name.Length + (name.Length % 2 == 0 ? 1 : 0)]; b[0] = (byte)b.Length; Both32(b, 2, (uint)lba); Both32(b, 10, (uint)size); Date.CopyTo(b, 18); b[25] = (byte)flags;
        b[28] = 1; b[31] = 1; b[32] = (byte)name.Length; name.CopyTo(b, 33); return b;
    }
    static byte[] PathTable(List<Entry> l, bool big)
    {
        var m = new MemoryStream();
        foreach (var e in l)
        {
            int nl = e.Name.Length; var b = new byte[8 + nl + (nl & 1)]; b[0] = (byte)nl; int parent = e.Parent != null ? e.Parent.Index : 1;
            if (big) { Be32(b, 2, (uint)e.Lba); b[6] = (byte)(parent >> 8); b[7] = (byte)parent; } else { BitConverter.GetBytes((uint)e.Lba).CopyTo(b, 2); b[6] = (byte)parent; b[7] = (byte)(parent >> 8); }
            e.Name.CopyTo(b, 8); m.Write(b, 0, b.Length);
        }
        return m.ToArray();
    }
    static byte[] DirData(Entry e, List<Entry> l, bool joliet)
    {
        var buf = new byte[e.Size]; int o = 0; Action<byte[]> put = r => { if (o % S + r.Length > S) o += S - o % S; r.CopyTo(buf, o); o += r.Length; };
        var p = e.Parent ?? e; put(Rec(e.Lba, e.Size, 2, new byte[] { 0 })); put(Rec(p.Lba, p.Size, 2, new byte[] { 1 }));
        foreach (var k in e.Sorted)
        {
            if (k.Dir) { var c = l.First(x => x.N == k); put(Rec(c.Lba, c.Size, 2, c.Name)); }
            else put(Rec(k.Lba, k.Size, 0, Enc(k, joliet)));
        }
        return buf;
    }
    static byte[] Vol(byte[] tpl, List<Entry> l, int ptSize, long lm, long big, long total)
    {
        var b = (byte[])tpl.Clone(); Both32(b, 80, (uint)total); Both32(b, 132, (uint)ptSize);
        BitConverter.GetBytes((uint)lm).CopyTo(b, 140); BitConverter.GetBytes(0u).CopyTo(b, 144); Be32(b, 148, (uint)big); Be32(b, 152, 0);
        Rec(l[0].Lba, l[0].Size, 2, new byte[] { 0 }).CopyTo(b, 156); return b;
    }
    static void Flatten(Node d, string path, List<KeyValuePair<string, Node>> o)
    {
        foreach (var k in d.Kids) { var r = path + "/" + k.Name; if (k.Dir) Flatten(k, r, o); else o.Add(new KeyValuePair<string, Node>(r, k)); }
    }
    public void Write(string output)
    {
        List<Entry> P = Tree(root, false), J = Tree(root, true);
        // table sizes do not depend on LBAs, so measure them with zeroed entries first
        byte[] pt = PathTable(P, false), jt = PathTable(J, false);
        long lba = 32, pL = lba; lba += Align(pt.Length); long pM = lba; lba += Align(pt.Length); long jL = lba; lba += Align(jt.Length); long jM = lba; lba += Align(jt.Length);
        foreach (var e in P) { e.Lba = lba; lba += e.Size / S; }
        foreach (var e in J) { e.Lba = lba; lba += e.Size / S; }
        var files = new List<KeyValuePair<string, Node>>(); Flatten(root, "", files); files.Sort((a, b) => string.CompareOrdinal(a.Key, b.Key));
        var oldLba = new Dictionary<Node, long>();
        foreach (var kv in files) { oldLba[kv.Value] = kv.Value.Lba; kv.Value.Lba = lba; lba += Align(kv.Value.Size); }
        long total = lba;
        using (var o = new FileStream(output, FileMode.Create, FileAccess.Write, FileShare.None, 1 << 20))
        {
            Action<byte[], long> put = (b, sec) => { o.Position = sec * S; o.Write(b, 0, b.Length); };
            var s0 = new byte[S]; Be32(s0, 0, 1); Be32(s0, 12, (uint)(total - 1)); put(s0, 0); put(s1, 1);
            put(Vol(pvd, P, pt.Length, pL, pM, total), 16); put(Vol(svd, J, jt.Length, jL, jM, total), 17); put(term, 18);
            put(PathTable(P, false), pL); put(PathTable(P, true), pM); put(PathTable(J, false), jL); put(PathTable(J, true), jM);
            foreach (var e in P) put(DirData(e, P, false), e.Lba);
            foreach (var e in J) put(DirData(e, J, true), e.Lba);
            foreach (var kv in files)
            {
                var n = kv.Value; o.Position = n.Lba * S;
                if (n.Src != null) using (var s = File.OpenRead(n.Src)) CopyRange(s, 0, n.Size, o);
                else CopyRange(f, oldLba[n] * S, n.Size, o);
            }
            o.SetLength(total * S);
        }
    }
    public void Dispose() { f.Close(); }
}

// Fetches the two encoding tools from their official sites into a temp folder. Nothing from either tool ships in this patcher.
static class Tools
{
    const string FfmpegUrl = "https://www.gyan.dev/ffmpeg/builds/ffmpeg-release-essentials.zip";
    const string RadUrl = "https://www.radgametools.com/down/Bink/RADTools.7z";
    const string RadPassword = "RAD"; // published on radgametools.com/bnkdown.htm

    static void Get(string url, string path)
    {
        ServicePointManager.SecurityProtocol = SecurityProtocolType.Tls12;
        var q = (HttpWebRequest)WebRequest.Create(url); q.UserAgent = "JerichoKO-Patcher"; q.Timeout = 60000; q.ReadWriteTimeout = 60000;
        using (var r = q.GetResponse()) using (var s = r.GetResponseStream()) using (var f = File.Create(path))
        {
            long total = r.ContentLength, got = 0; int next = 20, n; var buf = new byte[1 << 16];
            while ((n = s.Read(buf, 0, buf.Length)) > 0)
            {
                f.Write(buf, 0, n); got += n;
                if (total > 10000000 && got * 100 / total >= next) { Core.Log("  다운로드 " + next + "%"); next += 20; }
            }
            if (total > 0 && got != total) throw new Exception("다운로드가 중간에 끊겼습니다.");
        }
    }
    static string FileSha256(string p) { using (var h = SHA256.Create()) using (var f = File.OpenRead(p)) return BitConverter.ToString(h.ComputeHash(f)).Replace("-", "").ToLowerInvariant(); }

    static string Capture(string exe, string args)
    {
        var p = new ProcessStartInfo(exe, args) { UseShellExecute = false, CreateNoWindow = true, RedirectStandardOutput = true, RedirectStandardError = true };
        using (var x = Process.Start(p)) { x.ErrorDataReceived += (s, e) => { }; x.BeginErrorReadLine(); string o = x.StandardOutput.ReadToEnd(); x.WaitForExit(); return o; }
    }
    // the video step needs the subtitles filter (libass) and -fps_mode (ffmpeg 5.1+)
    public static bool FfmpegOk(string exe)
    {
        if (string.IsNullOrEmpty(exe) || !File.Exists(exe)) return false;
        try { return Regex.IsMatch(Capture(exe, "-hide_banner -filters"), @"\bsubtitles\b") && Capture(exe, "-hide_banner -h full").Contains("fps_mode"); }
        catch { return false; }
    }

    static string GetFfmpeg(string dir)
    {
        string zip = Path.Combine(dir, "ffmpeg.zip"), sum = zip + ".sha256", exe = Path.Combine(dir, "ffmpeg.exe");
        Core.Log("ffmpeg 내려받는 중 (gyan.dev, 약 115MB)...");
        Get(FfmpegUrl, zip); Get(FfmpegUrl + ".sha256", sum);
        if (FileSha256(zip) != File.ReadAllText(sum).Trim().Split(' ')[0].ToLowerInvariant()) throw new Exception("ffmpeg 파일의 SHA-256이 공식 값과 다릅니다.");
        using (var a = new ZipArchive(File.OpenRead(zip), ZipArchiveMode.Read))
        using (var s = a.Entries.First(e => e.Name.Equals("ffmpeg.exe", StringComparison.OrdinalIgnoreCase)).Open())
        using (var f = File.Create(exe)) s.CopyTo(f);
        File.Delete(zip);
        if (!FfmpegOk(exe)) throw new Exception("내려받은 ffmpeg에 자막 기능이 없습니다.");
        return exe;
    }
    static string GetRad(string dir)
    {
        string arc = Path.Combine(dir, "RADTools.7z"), setup = Path.Combine(dir, "radtools.exe"), inst = Path.Combine(dir, "rad");
        Core.Log("RAD Video Tools 내려받는 중 (radgametools.com, 약 1.2MB)...");
        Get(RadUrl, arc);
        File.WriteAllBytes(setup, SevenZip.ExtractSingle(File.ReadAllBytes(arc), RadPassword));
        Trust.Require(setup, "Epic Games", "RAD Game Tools");
        Directory.CreateDirectory(inst);
        // RunAsInvoker: unpack into temp as the normal user, with no UAC prompt and no system-wide install
        var p = new ProcessStartInfo(setup, "/S /D=" + inst) { UseShellExecute = false, CreateNoWindow = true }; p.EnvironmentVariables["__COMPAT_LAYER"] = "RunAsInvoker";
        using (var x = Process.Start(p)) { if (!x.WaitForExit(180000)) { x.Kill(); throw new Exception("RAD Video Tools 압축 해제가 끝나지 않습니다."); } }
        var rad = Path.Combine(inst, "radvideo64.exe");
        if (!File.Exists(rad)) throw new Exception("radvideo64.exe를 찾을 수 없습니다.");
        Trust.Require(rad, "Epic Games", "RAD Game Tools");
        return rad;
    }
    // ffmpeg/rad: an existing tool path, or null to fetch that tool for the duration of the job
    public static void With(string ffmpeg, string rad, Action<string, string> job)
    {
        string tmp = null;
        try
        {
            if (ffmpeg == null || rad == null)
            {
                tmp = Path.Combine(Path.GetTempPath(), "JerichoKO_tools_" + Guid.NewGuid().ToString("N")); Directory.CreateDirectory(tmp);
                try { if (ffmpeg == null) ffmpeg = GetFfmpeg(tmp); if (rad == null) rad = GetRad(tmp); }
                catch (Exception x) { throw new Exception("도구 자동 다운로드 실패: " + x.Message + "\r\n각 공식 사이트에서 직접 받아 경로를 지정하면 계속할 수 있습니다."); }
            }
            job(ffmpeg, rad);
        }
        finally { if (tmp != null) try { Directory.Delete(tmp, true); Core.Log("임시 도구 삭제 완료"); } catch { Core.Log("주의: 임시 폴더를 지우지 못했습니다: " + tmp); } }
    }
}

// Authenticode check via WinVerifyTrust, plus a publisher name match
static class Trust
{
    [StructLayout(LayoutKind.Sequential)] struct FileInfo { public uint Size; public IntPtr Path, Handle, Subject; }
    [StructLayout(LayoutKind.Sequential)] struct Data { public uint Size; public IntPtr Policy, Sip; public uint Ui, Revocation, Union; public IntPtr File; public uint State; public IntPtr StateData, Url; public uint Prov, Context; public IntPtr Settings; }
    [DllImport("wintrust.dll", CharSet = CharSet.Unicode)] static extern int WinVerifyTrust(IntPtr hwnd, [MarshalAs(UnmanagedType.LPStruct)] Guid action, ref Data data);
    public static void Require(string path, params string[] publishers)
    {
        var p = Marshal.StringToHGlobalUni(path); var fi = new FileInfo { Size = (uint)Marshal.SizeOf(typeof(FileInfo)), Path = p };
        var m = Marshal.AllocHGlobal(Marshal.SizeOf(typeof(FileInfo)));
        try
        {
            Marshal.StructureToPtr(fi, m, false);
            var d = new Data { Size = (uint)Marshal.SizeOf(typeof(Data)), Ui = 2, Union = 1, File = m };
            if (WinVerifyTrust(IntPtr.Zero, new Guid("00AAC56B-CD44-11d0-8CC2-00C04FC295EE"), ref d) != 0) throw new Exception(Path.GetFileName(path) + "의 디지털 서명이 유효하지 않습니다.");
            string subject = System.Security.Cryptography.X509Certificates.X509Certificate.CreateFromSignedFile(path).Subject;
            if (!publishers.Any(subject.Contains)) throw new Exception(Path.GetFileName(path) + "의 서명자가 예상과 다릅니다: " + subject);
        }
        finally { Marshal.FreeHGlobal(p); Marshal.FreeHGlobal(m); }
    }
}

// Reads a .7z holding one file through a chain of AES-256 / LZMA2 / BCJ-x86 coders.
// Windows 10's tar.exe cannot read this, and no 7-Zip install can be assumed.
static class SevenZip
{
    static long Num(byte[] b, ref int p)
    {
        int first = b[p++], mask = 0x80; long v = 0;
        for (int i = 0; i < 8; i++) { if ((first & mask) == 0) return v + ((long)(first & (mask - 1)) << (8 * i)); v |= (long)b[p++] << (8 * i); mask >>= 1; }
        return v;
    }
    static void Expect(byte[] b, ref int p, int v) { if (b[p++] != v) throw new Exception("지원하지 않는 7z 구조입니다."); }
    class Coder { public string Id; public byte[] Props; public int OutSize; }
    public static byte[] ExtractSingle(byte[] a, string password)
    {
        int p = 32 + (int)BitConverter.ToInt64(a, 12);
        Expect(a, ref p, 1); Expect(a, ref p, 4); Expect(a, ref p, 6);
        int dataStart = 32 + (int)Num(a, ref p); if (Num(a, ref p) != 1) throw new Exception("지원하지 않는 7z 구조입니다.");
        Expect(a, ref p, 9); int packSize = (int)Num(a, ref p); Expect(a, ref p, 0);
        Expect(a, ref p, 7); Expect(a, ref p, 11); if (Num(a, ref p) != 1) throw new Exception("지원하지 않는 7z 구조입니다."); Expect(a, ref p, 0);
        int n = (int)Num(a, ref p); var coders = new Coder[n];
        for (int i = 0; i < n; i++)
        {
            int flag = a[p++]; if ((flag & 0x10) != 0) throw new Exception("지원하지 않는 7z 구조입니다.");
            var c = new Coder { Id = BitConverter.ToString(a, p, flag & 15).Replace("-", ""), Props = new byte[0] }; p += flag & 15;
            if ((flag & 0x20) != 0) { int l = (int)Num(a, ref p); c.Props = new byte[l]; Array.Copy(a, p, c.Props, 0, l); p += l; }
            coders[i] = c;
        }
        var nextOf = new int[n]; for (int i = 0; i < n; i++) nextOf[i] = -1; var bound = new bool[n];
        for (int i = 0; i < n - 1; i++) { int inp = (int)Num(a, ref p), o = (int)Num(a, ref p); nextOf[o] = inp; bound[inp] = true; }
        Expect(a, ref p, 12); foreach (var c in coders) c.OutSize = (int)Num(a, ref p);
        var d = new byte[packSize]; Array.Copy(a, dataStart, d, 0, packSize);
        for (int i = Array.IndexOf(bound, false); i >= 0; i = nextOf[i])
        {
            var c = coders[i];
            if (c.Id == "06F10701") d = Aes(d, c.Props, password);
            else if (c.Id == "21") d = Lzma2(d, c.OutSize);
            else if (c.Id == "03030103") X86(d);
            else throw new Exception("지원하지 않는 7z 압축 방식입니다: " + c.Id);
            if (d.Length != c.OutSize) Array.Resize(ref d, c.OutSize);
        }
        return d;
    }
    static byte[] Aes(byte[] d, byte[] pr, string password)
    {
        int cycles = pr[0] & 0x3f, saltLen = ((pr[0] >> 7) & 1) + (pr[1] >> 4), ivLen = ((pr[0] >> 6) & 1) + (pr[1] & 15);
        var iv = new byte[16]; Array.Copy(pr, 2 + saltLen, iv, 0, ivLen);
        var seed = new byte[saltLen + password.Length * 2]; Array.Copy(pr, 2, seed, 0, saltLen); Encoding.Unicode.GetBytes(password).CopyTo(seed, saltLen);
        var block = new byte[seed.Length + 8]; seed.CopyTo(block, 0); byte[] key;
        using (var h = SHA256.Create())
        {
            for (long r = 0; r < 1L << cycles; r++) { BitConverter.GetBytes(r).CopyTo(block, seed.Length); h.TransformBlock(block, 0, block.Length, null, 0); }
            h.TransformFinalBlock(new byte[0], 0, 0); key = h.Hash;
        }
        using (var a = System.Security.Cryptography.Aes.Create())
        {
            a.Mode = CipherMode.CBC; a.Padding = PaddingMode.None; a.Key = key; a.IV = iv;
            using (var t = a.CreateDecryptor()) return t.TransformFinalBlock(d, 0, d.Length);
        }
    }
    static void X86(byte[] b)
    {
        bool[] allowed = { true, true, true, false, true, false, false, false }; int[] bitNum = { 0, 1, 2, 2, 3, 3, 3, 3 };
        uint mask = 0; int prev = -5, i = 0, limit = b.Length - 4;
        Func<byte, bool> ms = x => x == 0 || x == 0xFF;
        while (i < limit)
        {
            if (b[i] != 0xE8 && b[i] != 0xE9) { i++; continue; }
            int off = i - prev; prev = i;
            if (off > 5) mask = 0; else for (int k = 0; k < off; k++) { mask &= 0x77; mask <<= 1; }
            byte top = b[i + 4];
            if (ms(top) && allowed[(mask >> 1) & 7] && (mask >> 1) < 0x10)
            {
                uint src = (uint)top << 24 | (uint)b[i + 3] << 16 | (uint)b[i + 2] << 8 | b[i + 1], dest;
                while (true)
                {
                    dest = src - (uint)(i + 5);
                    if (mask == 0) break;
                    int idx = bitNum[mask >> 1];
                    if (!ms((byte)(dest >> (24 - idx * 8 - 8)))) break;
                    src = dest ^ ((1u << (32 - idx * 8)) - 1);
                }
                b[i + 4] = (byte)~(((dest >> 24) & 1) - 1); b[i + 3] = (byte)(dest >> 16); b[i + 2] = (byte)(dest >> 8); b[i + 1] = (byte)dest;
                i += 5; mask = 0;
            }
            else { i++; mask |= 1; if (ms(top)) mask |= 0x10; }
        }
    }

    // ---------- LZMA2 ----------
    const int IsRep = 192, RepG0 = 204, RepG1 = 216, RepG2 = 228, Rep0Long = 240, PosSlot = 432, Align = 688, PosDec = 704, LenA = 820, LenB = 1334, Lit = 1848;
    static byte[] Lzma2(byte[] s, int size)
    {
        var d = new Lz { O = new byte[size], S = s }; int p = 0;
        while (true)
        {
            int c = s[p++]; if (c == 0) break;
            if (c < 0x80)
            {
                if (c > 2) throw new Exception("LZMA2 데이터 오류");
                if (c == 1) d.DictStart = d.Op;
                int n = (s[p] << 8 | s[p + 1]) + 1; p += 2; Array.Copy(s, p, d.O, d.Op, n); p += n; d.Op += n; continue;
            }
            int un = ((c & 0x1f) << 16) + (s[p] << 8) + s[p + 1] + 1, pack = (s[p + 2] << 8) + s[p + 3] + 1, reset = (c >> 5) & 3; p += 4;
            if (reset == 3) d.DictStart = d.Op;
            if (reset >= 2) d.SetProps(s[p++]);
            if (reset >= 1) d.Reset();
            d.Sp = p; d.Decode(d.Op + un); p += pack;
        }
        return d.O;
    }
    class Lz
    {
        public byte[] O, S; public int Op, Sp, DictStart;
        int lc, lpMask, pbMask, st; uint range, code, r0, r1, r2, r3; ushort[] P;
        public void SetProps(int b) { lc = b % 9; b /= 9; pbMask = (1 << (b / 5)) - 1; int lp = b % 5; lpMask = (1 << lp) - 1; P = new ushort[Lit + (0x300 << (lc + lp))]; }
        public void Reset() { for (int i = 0; i < P.Length; i++) P[i] = 1024; st = 0; r0 = r1 = r2 = r3 = 0; }
        void Norm() { if (range < (1u << 24)) { range <<= 8; code = (code << 8) | S[Sp++]; } }
        int Bit(int i)
        {
            uint b = (range >> 11) * P[i]; int r;
            if (code < b) { range = b; P[i] = (ushort)(P[i] + ((2048 - P[i]) >> 5)); r = 0; }
            else { range -= b; code -= b; P[i] = (ushort)(P[i] - (P[i] >> 5)); r = 1; }
            Norm(); return r;
        }
        int Tree(int b, int bits) { int m = 1; for (int i = 0; i < bits; i++) m = (m << 1) + Bit(b + m); return m - (1 << bits); }
        int RevTree(int b, int bits) { int m = 1, sym = 0; for (int i = 0; i < bits; i++) { int x = Bit(b + m); m = (m << 1) + x; sym |= x << i; } return sym; }
        uint Direct(int n) { uint v = 0; while (n-- > 0) { range >>= 1; code -= range; uint t = 0 - (code >> 31); code += range & t; v = (v << 1) + t + 1; Norm(); } return v; }
        int Len(int b, int ps) { if (Bit(b) == 0) return Tree(b + 2 + ps * 8, 3); if (Bit(b + 1) == 0) return 8 + Tree(b + 130 + ps * 8, 3); return 16 + Tree(b + 258, 8); }
        public void Decode(int end)
        {
            range = 0xFFFFFFFF; code = 0; Sp++; for (int i = 0; i < 4; i++) code = (code << 8) | S[Sp++];
            while (Op < end)
            {
                int pos = Op - DictStart, ps = pos & pbMask;
                if (Bit((st << 4) + ps) == 0)
                {
                    int prev = Op > DictStart ? O[Op - 1] : 0, lb = Lit + 0x300 * (((pos & lpMask) << lc) + (prev >> (8 - lc))), sym = 1;
                    if (st >= 7)
                    {
                        int mb = O[Op - (int)r0 - 1];
                        do { int mbit = (mb >> 7) & 1; mb <<= 1; int x = Bit(lb + ((1 + mbit) << 8) + sym); sym = (sym << 1) | x; if (mbit != x) break; } while (sym < 0x100);
                    }
                    while (sym < 0x100) sym = (sym << 1) | Bit(lb + sym);
                    O[Op++] = (byte)sym; st = st < 4 ? 0 : st < 10 ? st - 3 : st - 6; continue;
                }
                int len;
                if (Bit(IsRep + st) == 0)
                {
                    r3 = r2; r2 = r1; r1 = r0; len = Len(LenA, ps); st = st < 7 ? 7 : 10;
                    int slot = Tree(PosSlot + (len < 4 ? len : 3) * 64, 6);
                    if (slot < 4) r0 = (uint)slot;
                    else
                    {
                        int n = (slot >> 1) - 1; uint dist = (uint)(2 | (slot & 1)) << n;
                        if (slot < 14) dist += (uint)RevTree(PosDec + (int)dist - slot, n);
                        else { dist += Direct(n - 4) << 4; dist += (uint)RevTree(Align, 4); }
                        r0 = dist;
                    }
                }
                else
                {
                    if (Bit(RepG0 + st) == 0)
                    {
                        if (Bit(Rep0Long + (st << 4) + ps) == 0) { st = st < 7 ? 9 : 11; O[Op] = O[Op - (int)r0 - 1]; Op++; continue; }
                    }
                    else
                    {
                        uint dist;
                        if (Bit(RepG1 + st) == 0) dist = r1;
                        else { if (Bit(RepG2 + st) == 0) dist = r2; else { dist = r3; r3 = r2; } r2 = r1; }
                        r1 = r0; r0 = dist;
                    }
                    len = Len(LenB, ps); st = st < 7 ? 8 : 11;
                }
                len += 2; if (r0 >= Op - DictStart) throw new Exception("LZMA2 데이터 오류");
                for (int i = 0; i < len; i++) { O[Op] = O[Op - (int)r0 - 1]; Op++; }
            }
        }
    }
}

class MainForm : Form
{
    TextBox game = Box(), rp = Box(), eb = Box(), ff = Box(), rad = Box(), log = new TextBox();
    RadioButton pc = new RadioButton { Text = "PC (RPCS3)", Checked = true, AutoSize = true }, hw = new RadioButton { Text = "PS3 실기 (커스텀 펌웨어)", AutoSize = true };
    CheckBox vid = new CheckBox { Text = "오프닝 영상에 한글 자막 넣기 (선택, 인터넷 필요, 10분 정도 소요)", AutoSize = true };
    Button go = new Button { Text = "설치", Width = 110, Height = 32 }, undo = new Button { Text = "되돌리기", Width = 110, Height = 32 }, elf = new Button { Text = "복호화 EBOOT 패치...", Width = 170, Height = 32 };
    static TextBox Box() { return new TextBox { Width = 470 }; }
    int y = 14;
    void Row(string label, TextBox t, bool file, string filter)
    {
        Controls.Add(new Label { Text = label, Left = 12, Top = y + 3, Width = 120 }); t.Left = 135; t.Top = y; Controls.Add(t);
        var b = new Button { Text = "찾기", Left = 612, Top = y - 1, Width = 60 }; Controls.Add(b);
        b.Click += (s, e) => { if (file) { var d = new OpenFileDialog { Filter = filter }; if (d.ShowDialog() == DialogResult.OK) t.Text = d.FileName; } else { var d = new FolderBrowserDialog(); if (d.ShowDialog() == DialogResult.OK) t.Text = d.SelectedPath; } };
        y += 32;
    }
    public MainForm()
    {
        Text = "Clive Barker's Jericho 한글 패처 (BLUS30063)"; ClientSize = new Size(690, 500); FormBorderStyle = FormBorderStyle.FixedSingle; MaximizeBox = false; Font = new Font("Malgun Gothic", 9);
        Controls.Add(new Label { Text = "게임 폴더 / ISO", Left = 12, Top = y + 3, Width = 120 }); game.Left = 135; game.Top = y; game.Width = 405; Controls.Add(game);
        var pickFolder = new Button { Text = "폴더", Left = 547, Top = y - 1, Width = 60 }; var pickIso = new Button { Text = "ISO", Left = 612, Top = y - 1, Width = 60 }; Controls.Add(pickFolder); Controls.Add(pickIso);
        pickFolder.Click += (s, e) => { var d = new FolderBrowserDialog(); if (d.ShowDialog() == DialogResult.OK) game.Text = d.SelectedPath; };
        pickIso.Click += (s, e) => { var d = new OpenFileDialog { Filter = "PS3 ISO (*.iso)|*.iso" }; if (d.ShowDialog() == DialogResult.OK) game.Text = d.FileName; };
        y += 32;
        pc.Left = 135; pc.Top = y; hw.Left = 280; hw.Top = y; Controls.Add(pc); Controls.Add(hw); y += 30;
        Row("RPCS3 폴더", rp, false, null);
        Row("재서명 EBOOT", eb, true, "재서명 EBOOT|*.BIN|모든 파일|*.*"); eb.Enabled = false;
        vid.Left = 135; vid.Top = y; Controls.Add(vid); y += 28;
        Row("ffmpeg.exe", ff, true, "ffmpeg|ffmpeg.exe"); Row("radvideo64.exe", rad, true, "RAD Video Tools|radvideo64.exe");
        Controls.Add(new Label { Text = "도구 경로를 비워 두면 공식 사이트에서 자동으로 받아 쓰고, 끝나면 지웁니다.", Left = 135, Top = y - 4, AutoSize = true }); y += 20;
        go.Left = 135; go.Top = y; undo.Left = 255; undo.Top = y; elf.Left = 375; elf.Top = y; Controls.AddRange(new Control[] { go, undo, elf }); y += 42;
        log.Multiline = true; log.ReadOnly = true; log.ScrollBars = ScrollBars.Vertical; log.Left = 12; log.Top = y; log.Width = 660; log.Height = 490 - y; Controls.Add(log);
        Core.Log = s => { if (IsDisposed) return; BeginInvoke((Action)(() => log.AppendText(s + "\r\n"))); };
        pc.CheckedChanged += (s, e) => { rp.Enabled = pc.Checked; eb.Enabled = !pc.Checked; };
        Func<string, string> onPath = n => (Environment.GetEnvironmentVariable("PATH") ?? "").Split(';').Select(d => { try { return Path.Combine(d.Trim(), n); } catch { return ""; } }).FirstOrDefault(File.Exists) ?? "";
        ff.Text = onPath("ffmpeg.exe"); rad.Text = onPath("radvideo64.exe");
        go.Click += (s, e) =>
        {
            bool getFf = false, getRad = false;
            if (vid.Checked)
            {
                getFf = !Tools.FfmpegOk(ff.Text); getRad = !File.Exists(rad.Text);
                if ((getFf || getRad) && MessageBox.Show(this, Consent(getFf, getRad), Text, MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button2) != DialogResult.Yes) { Core.Log("취소했습니다. 도구 경로를 직접 지정하거나 영상 자막 체크를 해제해 주세요."); return; }
            }
            string ff0 = getFf ? null : ff.Text, rad0 = getRad ? null : rad.Text;
            if (Core.IsIso(game.Text))
            {
                Job(() =>
                {
                    if (pc.Checked) Core.InstallRpcs3(rp.Text); // first: it is instant and fails on a wrong folder before the long ISO build
                    Action<string> video = null; if (vid.Checked) video = u => Tools.With(ff0, rad0, (f, r) => Core.InstallVideo(u, f, r));
                    string signed = !pc.Checked && eb.Text.Trim().Length > 0 ? eb.Text.Trim() : null;
                    Core.InstallIso(game.Text, video, signed);
                    Core.Log(pc.Checked ? "설치가 끝났습니다. RPCS3에서 위의 한글 ISO를 실행하세요." : signed != null ? "설치가 끝났습니다. 위의 한글 ISO를 PS3로 옮겨 webMAN 등으로 실행하세요." : "설치가 끝났습니다. 위의 한글 ISO를 PS3로 옮겨 webMAN 등으로 실행하세요. 글꼴 수정은 README를 참고하세요.");
                });
                return;
            }
            if (hw.Checked && eb.Text.Trim().Length > 0) Core.Log("주의: 재서명 EBOOT 칸은 ISO로 설치할 때만 사용합니다. 폴더 설치에서는 USRDIR의 EBOOT.BIN을 직접 교체해 주세요.");
            Job(() => { var u = Core.UsrDir(game.Text); Core.InstallText(u); if (pc.Checked) Core.InstallRpcs3(rp.Text); if (vid.Checked) Tools.With(ff0, rad0, (f, r) => Core.InstallVideo(u, f, r)); Core.AddSplash(u); Core.Log(pc.Checked ? "설치가 끝났습니다. RPCS3에서 원본 EBOOT.BIN으로 실행하세요." : "설치가 끝났습니다. 폴더를 PS3로 옮겨 webMAN 등으로 실행하세요. 글꼴 수정은 README를 참고하세요."); });
        };
        undo.Click += (s, e) => Job(() => Core.Uninstall(Core.IsIso(game.Text) ? null : Core.UsrDir(game.Text), rp.Text));
        elf.Click += (s, e) => { var d = new OpenFileDialog { Filter = "복호화 EBOOT (*.elf;*.bin)|*.elf;*.bin|모든 파일|*.*" }; if (d.ShowDialog() == DialogResult.OK) Job(() => Core.PatchElf(d.FileName)); };
    }
    static string Consent(bool getFf, bool getRad)
    {
        var s = new StringBuilder("영상 자막을 만들려면 아래 무료 도구가 필요합니다.\r\n공식 사이트에서 받아 임시 폴더에서 사용하고, 작업이 끝나면 지웁니다.\r\n\r\n");
        if (getFf) s.Append("• ffmpeg (gyan.dev, 약 115MB, GPL 라이선스)\r\n");
        if (getRad) s.Append("• RAD Video Tools (radgametools.com, 약 1.2MB)\r\n");
        if (getRad) s.Append("\r\nRAD Video Tools 사용권의 주요 제한:\r\n재배포 금지, 대여·재판매 금지, 수정·역공학 금지, 허가 없는 상업적 사용 금지\r\n");
        return s.Append("\r\n위 내용에 동의하고 내려받을까요?").ToString();
    }
    void Job(Action a)
    {
        go.Enabled = undo.Enabled = elf.Enabled = false;
        new Thread(() => { try { a(); } catch (Exception x) { Core.Log("오류: " + x.Message); } BeginInvoke((Action)(() => go.Enabled = undo.Enabled = elf.Enabled = true)); }) { IsBackground = true }.Start();
    }
}

static class Program
{
    [STAThread]
    static int Main(string[] a)
    {
        if (a.Length == 0) { Application.EnableVisualStyles(); Application.Run(new MainForm()); return 0; }
        // command line: --game D --rpcs3 D --ffmpeg F --rad F --log F [--video] [--uninstall] [--elf F]
        // with --video, a tool whose path is left out is downloaded (running the command accepts the RAD EULA)
        var o = new Dictionary<string, string>(); for (int i = 0; i < a.Length; i++) { if (a[i] == "--video" || a[i] == "--uninstall") o[a[i]] = "1"; else o[a[i]] = a[++i]; }
        Func<string, string> G = k => o.ContainsKey(k) ? o[k] : null;
        var w = new StreamWriter(G("--log") ?? "patcher.log", false, new UTF8Encoding(false)) { AutoFlush = true }; Core.Log = w.WriteLine;
        try
        {
            if (G("--elf") != null) { Core.PatchElf(G("--elf")); return 0; }
            if (Core.IsIso(G("--game")))
            {
                if (G("--uninstall") != null) { Core.Uninstall(null, G("--rpcs3")); return 0; }
                if (G("--rpcs3") != null) Core.InstallRpcs3(G("--rpcs3"));
                Action<string> video = null; if (G("--video") != null) video = d => Tools.With(G("--ffmpeg"), G("--rad"), (f, r) => Core.InstallVideo(d, f, r));
                Core.InstallIso(G("--game"), video, G("--eboot")); w.WriteLine("OK"); return 0;
            }
            var u = Core.UsrDir(G("--game"));
            if (G("--uninstall") != null) { Core.Uninstall(u, G("--rpcs3")); return 0; }
            Core.InstallText(u); if (G("--rpcs3") != null) Core.InstallRpcs3(G("--rpcs3")); if (G("--video") != null) Tools.With(G("--ffmpeg"), G("--rad"), (f, r) => Core.InstallVideo(u, f, r)); Core.AddSplash(u);
            w.WriteLine("OK"); return 0;
        }
        catch (Exception x) { w.WriteLine("ERROR " + x); return 1; }
    }
}
