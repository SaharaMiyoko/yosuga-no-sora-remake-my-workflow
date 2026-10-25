/* SPDX-License-Identifier: MIT */
/*
 * Linux native bootstrap page (data externalization).
 *
 * Implements the same 1920x1080 visual layout, artwork, proxy presets,
 * concurrent Range download + SHA-256 verification + serial extraction
 * pipeline, multi-part completeness gate, and local .zip / data.xp3 import
 * flow as src/core/sdl2/ios/IOSBootstrap.mm, BootstrapActivity.java, and
 * ohos-project/entry/src/main/ets/pages/Index.ets.
 */

#ifndef _FILE_OFFSET_BITS
#define _FILE_OFFSET_BITS 64
#endif

#include "LinuxBootstrap.h"

#if defined(__linux__) && !defined(__ANDROID__) && !defined(__OHOS__)

/* Include <png.h> before <csetjmp> so older libpng headers never complain
 * about setjmp.h already being included. */
#include <png.h>
#include <ft2build.h>
#include FT_FREETYPE_H
#include <SDL.h>

#include "../zip_extract.h"
#include "../xp3_extract.h"

#include <dlfcn.h>
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <condition_variable>
#include <csetjmp>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <functional>
#include <map>
#include <memory>
#include <mutex>
#include <set>
#include <string>
#include <thread>
#include <vector>

#ifndef KRKRSDL2_LINUX_APP_ID
#define KRKRSDL2_LINUX_APP_ID "com.shuimo0413.yosuganosora.hdremake"
#endif

#ifndef KRKRSDL2_DEFAULT_DATA_REPO
#define KRKRSDL2_DEFAULT_DATA_REPO "SaharaMiyoko/yosuga-no-sora-remake-my-workflow"
#endif

namespace {

static const int kDesignW = 1920;
static const int kDesignH = 1080;
static const int kPartConcurrency = 6;
static const int64_t kMinParallelSize = 4LL * 1024 * 1024;

static std::string g_activeDataRoot;

/* =========================================================================
 * Filesystem & String Helpers
 * ========================================================================= */

static std::string TrimStr(const std::string &s)
{
	size_t b = 0;
	while (b < s.size() && (unsigned char)s[b] <= 0x20) b++;
	size_t e = s.size();
	while (e > b && (unsigned char)s[e - 1] <= 0x20) e--;
	return s.substr(b, e - b);
}

static std::string ToLowerAscii(const std::string &s)
{
	std::string out = s;
	for (size_t i = 0; i < out.size(); ++i)
	{
		if (out[i] >= 'A' && out[i] <= 'Z')
			out[i] = (char)(out[i] - 'A' + 'a');
	}
	return out;
}

static bool EndsWithNoCase(const std::string &s, const std::string &suffix)
{
	if (s.size() < suffix.size()) return false;
	return ToLowerAscii(s.substr(s.size() - suffix.size())) == ToLowerAscii(suffix);
}

static std::string DirNameOf(const std::string &p)
{
	if (p.empty()) return "";
	size_t end = p.size();
	while (end > 1 && p[end - 1] == '/') end--;
	size_t slash = p.rfind('/', end - 1);
	if (slash == std::string::npos) return ".";
	if (slash == 0) return "/";
	return p.substr(0, slash);
}

static std::string BaseNameOf(const std::string &p)
{
	if (p.empty()) return "";
	size_t end = p.size();
	while (end > 1 && p[end - 1] == '/') end--;
	size_t slash = p.rfind('/', end - 1);
	if (slash == std::string::npos) return p.substr(0, end);
	return p.substr(slash + 1, end - slash - 1);
}

static bool IsRegularFile(const std::string &p)
{
	struct stat st;
	return stat(p.c_str(), &st) == 0 && S_ISREG(st.st_mode);
}

static bool IsDirectory(const std::string &p)
{
	struct stat st;
	return stat(p.c_str(), &st) == 0 && S_ISDIR(st.st_mode);
}

static bool PathExists(const std::string &p)
{
	struct stat st;
	return stat(p.c_str(), &st) == 0;
}

static int64_t FileSizeOf(const std::string &p)
{
	struct stat st;
	if (stat(p.c_str(), &st) != 0 || !S_ISREG(st.st_mode)) return -1;
	return (int64_t)st.st_size;
}

static bool EnsureDirRecursive(const std::string &dir)
{
	if (dir.empty() || dir == "/") return true;
	if (IsDirectory(dir)) return true;
	std::string parent = DirNameOf(dir);
	if (!parent.empty() && parent != dir && parent != ".")
	{
		if (!EnsureDirRecursive(parent)) return false;
	}
	if (mkdir(dir.c_str(), 0755) == 0 || errno == EEXIST)
		return IsDirectory(dir);
	return false;
}

static void RemoveTreeRecursive(const std::string &path)
{
	struct stat st;
	if (lstat(path.c_str(), &st) != 0) return;
	if (S_ISDIR(st.st_mode) && !S_ISLNK(st.st_mode))
	{
		DIR *d = opendir(path.c_str());
		if (d)
		{
			struct dirent *ent;
			while ((ent = readdir(d)) != nullptr)
			{
				if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0)
					continue;
				RemoveTreeRecursive(path + "/" + ent->d_name);
			}
			closedir(d);
		}
		rmdir(path.c_str());
	}
	else
	{
		unlink(path.c_str());
	}
}

static bool CopyRegularFile(const std::string &src, const std::string &dst, std::string *err)
{
	FILE *in = fopen(src.c_str(), "rb");
	if (!in)
	{
		if (err) *err = std::string("无法读取文件: ") + strerror(errno);
		return false;
	}
	EnsureDirRecursive(DirNameOf(dst));
	FILE *out = fopen(dst.c_str(), "wb");
	if (!out)
	{
		fclose(in);
		if (err) *err = std::string("无法写入文件: ") + strerror(errno);
		return false;
	}
	std::vector<uint8_t> buf(1024 * 1024);
	bool ok = true;
	for (;;)
	{
		size_t n = fread(buf.data(), 1, buf.size(), in);
		if (n > 0)
		{
			if (fwrite(buf.data(), 1, n, out) != n)
			{
				if (err) *err = std::string("写入失败: ") + strerror(errno);
				ok = false;
				break;
			}
		}
		if (n < buf.size())
		{
			if (ferror(in))
			{
				if (err) *err = std::string("读取失败: ") + strerror(errno);
				ok = false;
			}
			break;
		}
	}
	fclose(out);
	fclose(in);
	if (!ok) unlink(dst.c_str());
	return ok;
}

static bool MoveFileOrTree(const std::string &src, const std::string &dst, std::string *err)
{
	RemoveTreeRecursive(dst);
	EnsureDirRecursive(DirNameOf(dst));
	if (rename(src.c_str(), dst.c_str()) == 0)
		return true;
	if (errno != EXDEV)
	{
		if (err) *err = std::string("移动文件失败: ") + strerror(errno);
		return false;
	}
	struct stat st;
	if (lstat(src.c_str(), &st) != 0)
	{
		if (err) *err = std::string("读取源文件状态失败: ") + strerror(errno);
		return false;
	}
	if (S_ISDIR(st.st_mode) && !S_ISLNK(st.st_mode))
	{
		if (!EnsureDirRecursive(dst))
		{
			if (err) *err = "无法创建目标目录";
			return false;
		}
		DIR *d = opendir(src.c_str());
		if (!d)
		{
			if (err) *err = std::string("无法打开源目录: ") + strerror(errno);
			return false;
		}
		struct dirent *ent;
		while ((ent = readdir(d)) != nullptr)
		{
			if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0)
				continue;
			if (!MoveFileOrTree(src + "/" + ent->d_name, dst + "/" + ent->d_name, err))
			{
				closedir(d);
				return false;
			}
		}
		closedir(d);
		rmdir(src.c_str());
		return true;
	}
	if (!CopyRegularFile(src, dst, err))
		return false;
	unlink(src.c_str());
	return true;
}

static bool ReadWholeFile(const std::string &path, std::string &out)
{
	FILE *f = fopen(path.c_str(), "rb");
	if (!f) return false;
	if (fseek(f, 0, SEEK_END) != 0) { fclose(f); return false; }
	long sz = ftell(f);
	if (sz < 0 || sz > 32 * 1024 * 1024) { fclose(f); return false; }
	rewind(f);
	out.resize((size_t)sz);
	if (sz > 0 && fread(&out[0], 1, (size_t)sz, f) != (size_t)sz)
	{
		fclose(f);
		return false;
	}
	fclose(f);
	return true;
}

static bool WriteWholeFile(const std::string &path, const std::string &content)
{
	EnsureDirRecursive(DirNameOf(path));
	FILE *f = fopen(path.c_str(), "wb");
	if (!f) return false;
	bool ok = content.empty() || fwrite(content.data(), 1, content.size(), f) == content.size();
	fclose(f);
	return ok;
}

static std::string FormatBytes(double n)
{
	char buf[64];
	if (n < 1024.0)
		snprintf(buf, sizeof(buf), "%.0f B", n);
	else if (n < 1048576.0)
		snprintf(buf, sizeof(buf), "%.1f KB", n / 1024.0);
	else if (n < 1073741824.0)
		snprintf(buf, sizeof(buf), "%.1f MB", n / 1048576.0);
	else
		snprintf(buf, sizeof(buf), "%.2f GB", n / 1073741824.0);
	return buf;
}

static std::string GetExeDir()
{
	char buf[PATH_MAX];
	ssize_t n = readlink("/proc/self/exe", buf, sizeof(buf) - 1);
	if (n > 0)
	{
		buf[n] = '\0';
		return DirNameOf(std::string(buf));
	}
	char *base = SDL_GetBasePath();
	if (base)
	{
		std::string s(base);
		SDL_free(base);
		while (s.size() > 1 && s.back() == '/') s.pop_back();
		return s;
	}
	return ".";
}

static std::string ResolveXdgDataRoot()
{
	const char *overrideDir = getenv("KRKR_LINUX_DATA_DIR");
	if (overrideDir && overrideDir[0])
	{
		std::string r(overrideDir);
		while (r.size() > 1 && r.back() == '/') r.pop_back();
		return r;
	}
	std::string base;
	const char *xdg = getenv("XDG_DATA_HOME");
	if (xdg && xdg[0])
	{
		base = xdg;
	}
	else
	{
		const char *home = getenv("HOME");
		if (home && home[0])
			base = std::string(home) + "/.local/share";
		else
			base = "/tmp";
	}
	while (base.size() > 1 && base.back() == '/') base.pop_back();
	return base + "/" + KRKRSDL2_LINUX_APP_ID;
}

static bool HasPlayableDataInRoot(const std::string &root)
{
	if (root.empty()) return false;
	if (IsDirectory(root + "/content-data") && IsRegularFile(root + "/content-data/startup.tjs"))
		return true;
	if (IsRegularFile(root + "/content-data"))
		return true;
	if (IsRegularFile(root + "/data.xp3"))
		return true;
	if (IsRegularFile(root + "/data.exe"))
		return true;
	if (IsRegularFile(root + "/data/startup.tjs"))
		return true;
	if (IsRegularFile(root + "/data"))
		return true;
	return false;
}

/* =========================================================================
 * Pure C++ FIPS 180-4 SHA-256
 * ========================================================================= */

class Sha256 {
public:
	Sha256() { Reset(); }

	void Reset()
	{
		s_[0] = 0x6a09e667u; s_[1] = 0xbb67ae85u;
		s_[2] = 0x3c6ef372u; s_[3] = 0xa54ff53au;
		s_[4] = 0x510e527fu; s_[5] = 0x9b05688cu;
		s_[6] = 0x1f83d9abu; s_[7] = 0x5be0cd19u;
		totalLen_ = 0;
		bufLen_ = 0;
	}

	void Update(const uint8_t *data, size_t len)
	{
		totalLen_ += len;
		if (bufLen_ > 0)
		{
			size_t take = std::min(len, 64 - bufLen_);
			memcpy(buf_ + bufLen_, data, take);
			bufLen_ += take;
			data += take;
			len -= take;
			if (bufLen_ == 64)
			{
				Transform(buf_);
				bufLen_ = 0;
			}
		}
		while (len >= 64)
		{
			Transform(data);
			data += 64;
			len -= 64;
		}
		if (len > 0)
		{
			memcpy(buf_, data, len);
			bufLen_ = len;
		}
	}

	std::string FinalHex()
	{
		uint64_t bitLen = totalLen_ * 8ULL;
		uint8_t pad = 0x80;
		Update(&pad, 1);
		uint8_t zero = 0;
		while (bufLen_ != 56)
			Update(&zero, 1);
		uint8_t lenBytes[8];
		for (int i = 0; i < 8; ++i)
			lenBytes[i] = (uint8_t)((bitLen >> ((7 - i) * 8)) & 0xFFu);
		Update(lenBytes, 8);

		char hex[65];
		for (int i = 0; i < 8; ++i)
			snprintf(hex + i * 8, 9, "%08x", s_[i]);
		hex[64] = '\0';
		return std::string(hex);
	}

private:
	static inline uint32_t Ror(uint32_t x, uint32_t n) { return (x >> n) | (x << (32 - n)); }

	void Transform(const uint8_t block[64])
	{
		static const uint32_t k[64] = {
			0x428a2f98u,0x71374491u,0xb5c0fbcfu,0xe9b5dba5u,0x3956c25bu,0x59f111f1u,0x923f82a4u,0xab1c5ed5u,
			0xd807aa98u,0x12835b01u,0x243185beu,0x550c7dc3u,0x72be5d74u,0x80deb1feu,0x9bdc06a7u,0xc19bf174u,
			0xe49b69c1u,0xefbe4786u,0x0fc19dc6u,0x240ca1ccu,0x2de92c6fu,0x4a7484aau,0x5cb0a9dcu,0x76f988dau,
			0x983e5152u,0xa831c66du,0xb00327c8u,0xbf597fc7u,0xc6e00bf3u,0xd5a79147u,0x06ca6351u,0x14292967u,
			0x27b70a85u,0x2e1b2138u,0x4d2c6dfcu,0x53380d13u,0x650a7354u,0x766a0abbu,0x81c2c92eu,0x92722c85u,
			0xa2bfe8a1u,0xa81a664bu,0xc24b8b70u,0xc76c51a3u,0xd192e819u,0xd6990624u,0xf40e3585u,0x106aa070u,
			0x19a4c116u,0x1e376c08u,0x2748774cu,0x34b0bcb5u,0x391c0cb3u,0x4ed8aa4au,0x5b9cca4fu,0x682e6ff3u,
			0x748f82eeu,0x78a5636fu,0x84c87814u,0x8cc70208u,0x90befffau,0xa4506cebu,0xbef9a3f7u,0xc67178f2u
		};
		uint32_t w[64];
		for (int i = 0; i < 16; ++i)
		{
			w[i] = ((uint32_t)block[i * 4] << 24) |
			       ((uint32_t)block[i * 4 + 1] << 16) |
			       ((uint32_t)block[i * 4 + 2] << 8) |
			       ((uint32_t)block[i * 4 + 3]);
		}
		for (int i = 16; i < 64; ++i)
		{
			uint32_t s0 = Ror(w[i - 15], 7) ^ Ror(w[i - 15], 18) ^ (w[i - 15] >> 3);
			uint32_t s1 = Ror(w[i - 2], 17) ^ Ror(w[i - 2], 19) ^ (w[i - 2] >> 10);
			w[i] = w[i - 16] + s0 + w[i - 7] + s1;
		}
		uint32_t a = s_[0], b = s_[1], c = s_[2], d = s_[3];
		uint32_t e = s_[4], f = s_[5], g = s_[6], h = s_[7];
		for (int i = 0; i < 64; ++i)
		{
			uint32_t S1 = Ror(e, 6) ^ Ror(e, 11) ^ Ror(e, 25);
			uint32_t ch = (e & f) ^ ((~e) & g);
			uint32_t temp1 = h + S1 + ch + k[i] + w[i];
			uint32_t S0 = Ror(a, 2) ^ Ror(a, 13) ^ Ror(a, 22);
			uint32_t maj = (a & b) ^ (a & c) ^ (b & c);
			uint32_t temp2 = S0 + maj;
			h = g; g = f; f = e; e = d + temp1;
			d = c; c = b; b = a; a = temp1 + temp2;
		}
		s_[0] += a; s_[1] += b; s_[2] += c; s_[3] += d;
		s_[4] += e; s_[5] += f; s_[6] += g; s_[7] += h;
	}

	uint32_t s_[8];
	uint64_t totalLen_;
	size_t bufLen_;
	uint8_t buf_[64];
};

static std::string Sha256FileHex(const std::string &path, const std::atomic<bool> &cancelFlag)
{
	FILE *f = fopen(path.c_str(), "rb");
	if (!f) return "";
	Sha256 sha;
	std::vector<uint8_t> buf(1024 * 1024);
	for (;;)
	{
		if (cancelFlag.load()) { fclose(f); return ""; }
		size_t n = fread(buf.data(), 1, buf.size(), f);
		if (n > 0) sha.Update(buf.data(), n);
		if (n < buf.size())
		{
			if (ferror(f)) { fclose(f); return ""; }
			break;
		}
	}
	fclose(f);
	return sha.FinalHex();
}

/* =========================================================================
 * Minimal Recursive-Descent JSON Parser
 * ========================================================================= */

struct JsonVal {
	enum Type { kNull, kBool, kNumber, kString, kArray, kObject };
	Type type = kNull;
	bool bVal = false;
	double numVal = 0.0;
	int64_t intVal = 0;
	std::string strVal;
	std::vector<JsonVal> arrVal;
	std::map<std::string, JsonVal> objVal;

	const JsonVal *Get(const std::string &key) const
	{
		if (type != kObject) return nullptr;
		std::map<std::string, JsonVal>::const_iterator it = objVal.find(key);
		return it == objVal.end() ? nullptr : &it->second;
	}
	std::string GetStr(const std::string &key, const std::string &def = "") const
	{
		const JsonVal *v = Get(key);
		return (v && v->type == kString) ? v->strVal : def;
	}
	int64_t GetInt64(const std::string &key, int64_t def = 0) const
	{
		const JsonVal *v = Get(key);
		return (v && v->type == kNumber) ? v->intVal : def;
	}
	bool GetBool(const std::string &key, bool def = false) const
	{
		const JsonVal *v = Get(key);
		return (v && v->type == kBool) ? v->bVal : def;
	}
};

class JsonParser {
public:
	explicit JsonParser(const std::string &s) : s_(s), pos_(0) {}

	bool Parse(JsonVal &out)
	{
		SkipWs();
		if (pos_ + 3 <= s_.size() &&
		    (uint8_t)s_[pos_] == 0xEF && (uint8_t)s_[pos_ + 1] == 0xBB && (uint8_t)s_[pos_ + 2] == 0xBF)
		{
			pos_ += 3;
			SkipWs();
		}
		if (!ParseValue(out)) return false;
		SkipWs();
		return pos_ == s_.size();
	}

private:
	void SkipWs()
	{
		while (pos_ < s_.size() && (s_[pos_] == ' ' || s_[pos_] == '\t' || s_[pos_] == '\r' || s_[pos_] == '\n'))
			pos_++;
	}

	static void AppendUtf8(std::string &out, uint32_t cp)
	{
		if (cp <= 0x7Fu)
			out.push_back((char)cp);
		else if (cp <= 0x7FFu)
		{
			out.push_back((char)(0xC0u | (cp >> 6)));
			out.push_back((char)(0x80u | (cp & 0x3Fu)));
		}
		else if (cp <= 0xFFFFu)
		{
			out.push_back((char)(0xE0u | (cp >> 12)));
			out.push_back((char)(0x80u | ((cp >> 6) & 0x3Fu)));
			out.push_back((char)(0x80u | (cp & 0x3Fu)));
		}
		else if (cp <= 0x10FFFFu)
		{
			out.push_back((char)(0xF0u | (cp >> 18)));
			out.push_back((char)(0x80u | ((cp >> 12) & 0x3Fu)));
			out.push_back((char)(0x80u | ((cp >> 6) & 0x3Fu)));
			out.push_back((char)(0x80u | (cp & 0x3Fu)));
		}
	}

	bool ParseHex4(uint32_t &out)
	{
		if (pos_ + 4 > s_.size()) return false;
		out = 0;
		for (int i = 0; i < 4; ++i)
		{
			char c = s_[pos_++];
			out <<= 4;
			if (c >= '0' && c <= '9') out |= (uint32_t)(c - '0');
			else if (c >= 'a' && c <= 'f') out |= (uint32_t)(c - 'a' + 10);
			else if (c >= 'A' && c <= 'F') out |= (uint32_t)(c - 'A' + 10);
			else return false;
		}
		return true;
	}

	bool ParseString(std::string &out)
	{
		if (pos_ >= s_.size() || s_[pos_] != '"') return false;
		pos_++;
		out.clear();
		while (pos_ < s_.size())
		{
			char c = s_[pos_++];
			if (c == '"') return true;
			if (c == '\\')
			{
				if (pos_ >= s_.size()) return false;
				char esc = s_[pos_++];
				switch (esc)
				{
				case '"': out.push_back('"'); break;
				case '\\': out.push_back('\\'); break;
				case '/': out.push_back('/'); break;
				case 'b': out.push_back('\b'); break;
				case 'f': out.push_back('\f'); break;
				case 'n': out.push_back('\n'); break;
				case 'r': out.push_back('\r'); break;
				case 't': out.push_back('\t'); break;
				case 'u':
				{
					uint32_t cp = 0;
					if (!ParseHex4(cp)) return false;
					if (cp >= 0xD800u && cp <= 0xDBFFu && pos_ + 2 <= s_.size() &&
					    s_[pos_] == '\\' && s_[pos_ + 1] == 'u')
					{
						pos_ += 2;
						uint32_t low = 0;
						if (!ParseHex4(low)) return false;
						if (low >= 0xDC00u && low <= 0xDFFFu)
							cp = 0x10000u + (((cp - 0xD800u) << 10) | (low - 0xDC00u));
					}
					AppendUtf8(out, cp);
					break;
				}
				default: return false;
				}
			}
			else
			{
				out.push_back(c);
			}
		}
		return false;
	}

	bool ParseValue(JsonVal &out)
	{
		SkipWs();
		if (pos_ >= s_.size()) return false;
		char c = s_[pos_];
		if (c == '"')
		{
			out.type = JsonVal::kString;
			return ParseString(out.strVal);
		}
		if (c == '{')
		{
			out.type = JsonVal::kObject;
			out.objVal.clear();
			pos_++;
			SkipWs();
			if (pos_ < s_.size() && s_[pos_] == '}') { pos_++; return true; }
			for (;;)
			{
				SkipWs();
				std::string key;
				if (!ParseString(key)) return false;
				SkipWs();
				if (pos_ >= s_.size() || s_[pos_] != ':') return false;
				pos_++;
				JsonVal val;
				if (!ParseValue(val)) return false;
				out.objVal[key] = std::move(val);
				SkipWs();
				if (pos_ >= s_.size()) return false;
				if (s_[pos_] == '}') { pos_++; return true; }
				if (s_[pos_] != ',') return false;
				pos_++;
			}
		}
		if (c == '[')
		{
			out.type = JsonVal::kArray;
			out.arrVal.clear();
			pos_++;
			SkipWs();
			if (pos_ < s_.size() && s_[pos_] == ']') { pos_++; return true; }
			for (;;)
			{
				JsonVal elem;
				if (!ParseValue(elem)) return false;
				out.arrVal.push_back(std::move(elem));
				SkipWs();
				if (pos_ >= s_.size()) return false;
				if (s_[pos_] == ']') { pos_++; return true; }
				if (s_[pos_] != ',') return false;
				pos_++;
			}
		}
		if (s_.compare(pos_, 4, "true") == 0)
		{
			out.type = JsonVal::kBool;
			out.bVal = true;
			pos_ += 4;
			return true;
		}
		if (s_.compare(pos_, 5, "false") == 0)
		{
			out.type = JsonVal::kBool;
			out.bVal = false;
			pos_ += 5;
			return true;
		}
		if (s_.compare(pos_, 4, "null") == 0)
		{
			out.type = JsonVal::kNull;
			pos_ += 4;
			return true;
		}
		if (c == '-' || (c >= '0' && c <= '9'))
		{
			size_t start = pos_;
			if (s_[pos_] == '-') pos_++;
			while (pos_ < s_.size() && s_[pos_] >= '0' && s_[pos_] <= '9') pos_++;
			bool isFloat = false;
			if (pos_ < s_.size() && s_[pos_] == '.')
			{
				isFloat = true;
				pos_++;
				while (pos_ < s_.size() && s_[pos_] >= '0' && s_[pos_] <= '9') pos_++;
			}
			if (pos_ < s_.size() && (s_[pos_] == 'e' || s_[pos_] == 'E'))
			{
				isFloat = true;
				pos_++;
				if (pos_ < s_.size() && (s_[pos_] == '+' || s_[pos_] == '-')) pos_++;
				while (pos_ < s_.size() && s_[pos_] >= '0' && s_[pos_] <= '9') pos_++;
			}
			std::string numStr = s_.substr(start, pos_ - start);
			out.type = JsonVal::kNumber;
			out.numVal = strtod(numStr.c_str(), nullptr);
			out.intVal = isFloat ? (int64_t)out.numVal : (int64_t)strtoll(numStr.c_str(), nullptr, 10);
			return pos_ > start;
		}
		return false;
	}

	const std::string &s_;
	size_t pos_;
};

static bool ParseJson(const std::string &text, JsonVal &out)
{
	JsonParser p(text);
	return p.Parse(out);
}

/* =========================================================================
 * Multi-Part Pack Completeness & Merge Into Data Dir (Mirrors IOSBootstrap)
 * ========================================================================= */

static bool ParsePackCounts(const std::string &jsonPath, int &outIdx, int &outCnt)
{
	std::string text;
	if (!ReadWholeFile(jsonPath, text)) return false;
	JsonVal v;
	if (!ParseJson(text, v) || v.type != JsonVal::kObject) return false;
	int idx = (int)v.GetInt64("packIndex", 0);
	int cnt = (int)v.GetInt64("packCount", 0);
	if (idx <= 0 || cnt <= 0) return false;
	outIdx = idx;
	outCnt = cnt;
	return true;
}

static std::vector<int> MissingPackIndices(const std::string &appRoot, int knownPackCount)
{
	std::set<int> have;
	int maxCount = knownPackCount;
	DIR *d = opendir(appRoot.c_str());
	if (d)
	{
		struct dirent *ent;
		while ((ent = readdir(d)) != nullptr)
		{
			std::string name(ent->d_name);
			if (name.compare(0, 12, "data-assets-") == 0 && EndsWithNoCase(name, ".json"))
			{
				int idx = 0, cnt = 0;
				if (ParsePackCounts(appRoot + "/" + name, idx, cnt))
				{
					have.insert(idx);
					if (cnt > maxCount) maxCount = cnt;
				}
			}
		}
		closedir(d);
	}
	std::vector<int> missing;
	if (maxCount > 1)
	{
		for (int i = 1; i <= maxCount; ++i)
		{
			if (have.find(i) == have.end())
				missing.push_back(i);
		}
	}
	return missing;
}

static std::string FormatPackIndexList(const std::vector<int> &indices)
{
	std::string s = "第 ";
	for (size_t i = 0; i < indices.size(); ++i)
	{
		if (i > 0) s += "、";
		s += std::to_string(indices[i]);
	}
	s += " 个分包";
	return s;
}

static void ClearPackRecords(const std::string &appRoot)
{
	DIR *d = opendir(appRoot.c_str());
	if (!d) return;
	struct dirent *ent;
	while ((ent = readdir(d)) != nullptr)
	{
		std::string name(ent->d_name);
		if (name.compare(0, 12, "data-assets-") == 0 && EndsWithNoCase(name, ".json"))
			unlink((appRoot + "/" + name).c_str());
	}
	closedir(d);
}

static bool MergeDirTree(const std::string &src, const std::string &dst, std::string *err)
{
	if (!EnsureDirRecursive(dst))
	{
		if (err) *err = "无法创建数据目录: " + dst;
		return false;
	}
	DIR *d = opendir(src.c_str());
	if (!d)
	{
		if (err) *err = std::string("无法读取解压临时目录: ") + strerror(errno);
		return false;
	}
	struct dirent *ent;
	while ((ent = readdir(d)) != nullptr)
	{
		if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0)
			continue;
		std::string sp = src + "/" + ent->d_name;
		std::string dp = dst + "/" + ent->d_name;
		struct stat st;
		if (lstat(sp.c_str(), &st) == 0 && S_ISDIR(st.st_mode) && !S_ISLNK(st.st_mode))
		{
			if (!MergeDirTree(sp, dp, err))
			{
				closedir(d);
				return false;
			}
		}
		else
		{
			if (!MoveFileOrTree(sp, dp, err))
			{
				closedir(d);
				return false;
			}
		}
	}
	closedir(d);
	return true;
}

static bool MergeIntoDataDir(const std::string &stageDir, const std::string &appRoot,
                             int *outPackIdx, int *outPackCnt, std::string *err)
{
	std::string packMeta = stageDir + "/data-assets.json";
	if (IsRegularFile(packMeta))
	{
		int idx = 0, cnt = 0;
		if (ParsePackCounts(packMeta, idx, cnt))
		{
			if (outPackIdx) *outPackIdx = idx;
			if (outPackCnt) *outPackCnt = cnt;
			std::string dstMeta = appRoot + "/data-assets-" + std::to_string(idx) + ".json";
			MoveFileOrTree(packMeta, dstMeta, nullptr);
		}
		unlink(packMeta.c_str());
	}
	std::string nestedData = stageDir + "/data";
	std::string srcRoot = IsDirectory(nestedData) ? nestedData : stageDir;
	return MergeDirTree(srcRoot, appRoot + "/data", err);
}

/* =========================================================================
 * Dynamic libcurl + CLI Fallback HTTP Engine (Zero Distro Soname Fragility)
 * ========================================================================= */

class HttpEngine {
public:
	typedef std::function<void(int64_t done, int64_t total)> ProgressFn;

	HttpEngine() : handle_(nullptr), ready_(false)
	{
		const char *candidates[] = {
			"libcurl.so.4",
			"libcurl-gnutls.so.4",
			"libcurl-nss.so.4",
			"libcurl.so",
			nullptr
		};
		for (int i = 0; candidates[i]; ++i)
		{
			handle_ = dlopen(candidates[i], RTLD_LAZY | RTLD_LOCAL);
			if (handle_) break;
		}
		if (!handle_) return;

		global_init_ = ( GlobalInitFn )dlsym(handle_, "curl_global_init");
		easy_init_ = ( EasyInitFn )dlsym(handle_, "curl_easy_init");
		easy_setopt_ = ( EasySetoptFn )dlsym(handle_, "curl_easy_setopt");
		easy_perform_ = ( EasyPerformFn )dlsym(handle_, "curl_easy_perform");
		easy_getinfo_ = ( EasyGetinfoFn )dlsym(handle_, "curl_easy_getinfo");
		easy_cleanup_ = ( EasyCleanupFn )dlsym(handle_, "curl_easy_cleanup");
		easy_strerror_ = ( EasyStrerrorFn )dlsym(handle_, "curl_easy_strerror");

		if (global_init_ && easy_init_ && easy_setopt_ && easy_perform_ &&
		    easy_getinfo_ && easy_cleanup_)
		{
			global_init_(3L /* CURL_GLOBAL_ALL */);
			ready_ = true;
		}
	}

	~HttpEngine()
	{
		if (handle_) dlclose(handle_);
	}

	bool FetchBytes(const std::string &url, size_t maxBytes,
	                const std::atomic<bool> &cancelFlag,
	                std::string &outBody, std::string &outErr)
	{
		outBody.clear();
		if (ready_)
		{
			void *easy = easy_init_();
			if (easy)
			{
				MemWriteCtx ctx{ &outBody, maxBytes, &cancelFlag, false };
				ConfigureCommon(easy, url);
				easy_setopt_(easy, 20011 /* CURLOPT_WRITEFUNCTION */, (void *)&MemWriteCb);
				easy_setopt_(easy, 10001 /* CURLOPT_WRITEDATA */, (void *)&ctx);
				int rc = easy_perform_(easy);
				long httpCode = 0;
				easy_getinfo_(easy, 0x200002 /* CURLINFO_RESPONSE_CODE */, &httpCode);
				easy_cleanup_(easy);

				if (cancelFlag.load()) { outErr = "已取消"; return false; }
				if (rc == 0 && httpCode >= 200 && httpCode < 300)
					return true;
				if (httpCode >= 400)
					outErr = "HTTP " + std::to_string(httpCode);
				else
					outErr = easy_strerror_ ? easy_strerror_(rc) : ("网络错误 (" + std::to_string(rc) + ")");
				return false;
			}
		}
		return FetchBytesCli(url, cancelFlag, outBody, outErr);
	}

	bool DownloadFile(const std::string &url, const std::string &destPath,
	                  int64_t expectedSize, const std::atomic<bool> &cancelFlag,
	                  const ProgressFn &onProgress, std::string &outErr)
	{
		EnsureDirRecursive(DirNameOf(destPath));
		if (ready_ && expectedSize >= kMinParallelSize)
		{
			if (DownloadChunkedCurl(url, destPath, expectedSize, cancelFlag, onProgress))
				return true;
			if (cancelFlag.load()) { outErr = "已取消"; return false; }
			unlink(destPath.c_str());
		}
		if (ready_)
		{
			return DownloadStreamCurl(url, destPath, expectedSize, cancelFlag, onProgress, outErr);
		}
		return DownloadStreamCli(url, destPath, expectedSize, cancelFlag, onProgress, outErr);
	}

private:
	typedef int (*GlobalInitFn)(long);
	typedef void *(*EasyInitFn)(void);
	typedef int (*EasySetoptFn)(void *, int, ...);
	typedef int (*EasyPerformFn)(void *);
	typedef int (*EasyGetinfoFn)(void *, int, ...);
	typedef void (*EasyCleanupFn)(void *);
	typedef const char *(*EasyStrerrorFn)(int);

	struct MemWriteCtx {
		std::string *out;
		size_t maxBytes;
		const std::atomic<bool> *cancel;
		bool overflow;
	};

	static size_t MemWriteCb(char *ptr, size_t size, size_t nmemb, void *userdata)
	{
		MemWriteCtx *ctx = (MemWriteCtx *)userdata;
		if (ctx->cancel && ctx->cancel->load()) return 0;
		size_t total = size * nmemb;
		if (ctx->out->size() + total > ctx->maxBytes)
		{
			ctx->overflow = true;
			return 0;
		}
		ctx->out->append(ptr, total);
		return total;
	}

	struct StreamWriteCtx {
		FILE *fp;
		int64_t written;
		int64_t expected;
		const std::atomic<bool> *cancel;
		const ProgressFn *progress;
	};

	static size_t StreamWriteCb(char *ptr, size_t size, size_t nmemb, void *userdata)
	{
		StreamWriteCtx *ctx = (StreamWriteCtx *)userdata;
		if (ctx->cancel && ctx->cancel->load()) return 0;
		size_t total = size * nmemb;
		if (total > 0 && fwrite(ptr, 1, total, ctx->fp) != total)
			return 0;
		ctx->written += (int64_t)total;
		if (ctx->progress && *ctx->progress)
			(*ctx->progress)(ctx->written, ctx->expected);
		return total;
	}

	struct RangeWriteCtx {
		HttpEngine *self;
		void *easy;
		int fd;
		int64_t offset;
		int64_t limitOffset;
		bool requirePartial206;
		bool statusChecked;
		std::atomic<int64_t> *totalWritten;
		int64_t totalExpected;
		const std::atomic<bool> *cancel;
		std::atomic<bool> *rangeFailed;
		const ProgressFn *progress;
	};

	static size_t RangeWriteCb(char *ptr, size_t size, size_t nmemb, void *userdata)
	{
		RangeWriteCtx *ctx = (RangeWriteCtx *)userdata;
		if ((ctx->cancel && ctx->cancel->load()) || ctx->rangeFailed->load())
			return 0;
		if (!ctx->statusChecked)
		{
			ctx->statusChecked = true;
			long code = 0;
			ctx->self->easy_getinfo_(ctx->easy, 0x200002 /* CURLINFO_RESPONSE_CODE */, &code);
			if (ctx->requirePartial206 && code != 206)
			{
				/* Server or proxy ignored Range and returned 200 full body; abort
				 * chunked transfer cleanly so DownloadStreamCurl takes over. */
				ctx->rangeFailed->store(true);
				return 0;
			}
			if (code != 206 && code != 200)
			{
				ctx->rangeFailed->store(true);
				return 0;
			}
		}
		size_t total = size * nmemb;
		if (total == 0) return 0;
		if (ctx->offset + (int64_t)total > ctx->limitOffset)
		{
			ctx->rangeFailed->store(true);
			return 0;
		}
		size_t done = 0;
		while (done < total)
		{
			ssize_t w = pwrite(ctx->fd, ptr + done, total - done, (off_t)(ctx->offset + (int64_t)done));
			if (w <= 0)
			{
				if (w < 0 && errno == EINTR) continue;
				ctx->rangeFailed->store(true);
				return 0;
			}
			done += (size_t)w;
		}
		ctx->offset += (int64_t)total;
		int64_t cur = ctx->totalWritten->fetch_add((int64_t)total) + (int64_t)total;
		if (ctx->progress && *ctx->progress)
			(*ctx->progress)(cur, ctx->totalExpected);
		return total;
	}

	void ConfigureCommon(void *easy, const std::string &url)
	{
		easy_setopt_(easy, 10002 /* CURLOPT_URL */, url.c_str());
		easy_setopt_(easy, 10018 /* CURLOPT_USERAGENT */, "yosuga-linux-bootstrap/1.0");
		easy_setopt_(easy, 52 /* CURLOPT_FOLLOWLOCATION */, 1L);
		easy_setopt_(easy, 68 /* CURLOPT_MAXREDIRS */, 10L);
		easy_setopt_(easy, 78 /* CURLOPT_CONNECTTIMEOUT */, 20L);
		easy_setopt_(easy, 99 /* CURLOPT_NOSIGNAL */, 1L);
		easy_setopt_(easy, 19 /* CURLOPT_LOW_SPEED_LIMIT */, 1024L);
		easy_setopt_(easy, 20 /* CURLOPT_LOW_SPEED_TIME */, 45L);
	}

	bool DownloadChunkedCurl(const std::string &url, const std::string &destPath,
	                         int64_t expectedSize, const std::atomic<bool> &cancelFlag,
	                         const ProgressFn &onProgress)
	{
		int fd = open(destPath.c_str(), O_CREAT | O_TRUNC | O_RDWR, 0644);
		if (fd < 0) return false;
		if (ftruncate(fd, (off_t)expectedSize) != 0)
		{
			close(fd);
			return false;
		}

		std::atomic<int64_t> totalWritten(0);
		std::atomic<bool> rangeFailed(false);
		int64_t slice = (expectedSize + kPartConcurrency - 1) / kPartConcurrency;
		std::vector<std::thread> workers;

		for (int i = 0; i < kPartConcurrency; ++i)
		{
			int64_t start = slice * i;
			int64_t end = std::min(expectedSize, start + slice) - 1;
			if (start > end) break;

			workers.emplace_back([&, start, end]() {
				for (int attempt = 0; attempt < 3; ++attempt)
				{
					if (cancelFlag.load() || rangeFailed.load()) return;
					if (attempt > 0) usleep(400000 * attempt);

					void *easy = easy_init_();
					if (!easy) { rangeFailed.store(true); return; }

					int64_t beforeChunk = 0;
					RangeWriteCtx ctx{
						this, easy, fd, start, end + 1,
						start > 0, false, &totalWritten, expectedSize,
						&cancelFlag, &rangeFailed, &onProgress
					};
					std::string rangeSpec = std::to_string(start) + "-" + std::to_string(end);
					ConfigureCommon(easy, url);
					easy_setopt_(easy, 10007 /* CURLOPT_RANGE */, rangeSpec.c_str());
					easy_setopt_(easy, 20011 /* CURLOPT_WRITEFUNCTION */, (void *)&RangeWriteCb);
					easy_setopt_(easy, 10001 /* CURLOPT_WRITEDATA */, (void *)&ctx);

					int rc = easy_perform_(easy);
					long httpCode = 0;
					easy_getinfo_(easy, 0x200002 /* CURLINFO_RESPONSE_CODE */, &httpCode);
					easy_cleanup_(easy);

					beforeChunk = ctx.offset - start;
					if (rc == 0 && (httpCode == 206 || (start == 0 && httpCode == 200)) &&
					    ctx.offset == end + 1)
					{
						return;
					}
					if (beforeChunk > 0)
						totalWritten.fetch_sub(beforeChunk);
					if (rangeFailed.load()) return;
				}
				rangeFailed.store(true);
			});
		}

		for (size_t i = 0; i < workers.size(); ++i)
		{
			if (workers[i].joinable()) workers[i].join();
		}
		fsync(fd);
		close(fd);
		return !cancelFlag.load() && !rangeFailed.load() && totalWritten.load() == expectedSize;
	}

	bool DownloadStreamCurl(const std::string &url, const std::string &destPath,
	                        int64_t expectedSize, const std::atomic<bool> &cancelFlag,
	                        const ProgressFn &onProgress, std::string &outErr)
	{
		for (int attempt = 1; attempt <= 3; ++attempt)
		{
			if (cancelFlag.load()) { outErr = "已取消"; return false; }
			FILE *fp = fopen(destPath.c_str(), "wb");
			if (!fp)
			{
				outErr = std::string("无法创建下载文件: ") + strerror(errno);
				return false;
			}
			void *easy = easy_init_();
			if (!easy)
			{
				fclose(fp);
				outErr = "无法初始化网络请求";
				return false;
			}
			StreamWriteCtx ctx{ fp, 0, expectedSize, &cancelFlag, &onProgress };
			ConfigureCommon(easy, url);
			easy_setopt_(easy, 20011 /* CURLOPT_WRITEFUNCTION */, (void *)&StreamWriteCb);
			easy_setopt_(easy, 10001 /* CURLOPT_WRITEDATA */, (void *)&ctx);

			int rc = easy_perform_(easy);
			long httpCode = 0;
			easy_getinfo_(easy, 0x200002 /* CURLINFO_RESPONSE_CODE */, &httpCode);
			easy_cleanup_(easy);
			fclose(fp);

			if (cancelFlag.load())
			{
				unlink(destPath.c_str());
				outErr = "已取消";
				return false;
			}
			if (rc == 0 && httpCode >= 200 && httpCode < 300 &&
			    (expectedSize <= 0 || FileSizeOf(destPath) == expectedSize))
			{
				return true;
			}
			if (httpCode >= 400)
				outErr = "HTTP " + std::to_string(httpCode);
			else
				outErr = easy_strerror_ ? easy_strerror_(rc) : ("下载中断 (" + std::to_string(rc) + ")");
			if (attempt < 3) sleep(attempt * 2);
		}
		return false;
	}

	static bool RunCliDownload(const std::string &url, const std::string &destPath,
	                           int64_t expectedSize, const std::atomic<bool> &cancelFlag,
	                           const ProgressFn *onProgress, std::string &outErr)
	{
		unlink(destPath.c_str());
		pid_t pid = fork();
		if (pid < 0)
		{
			outErr = "无法创建下载子进程";
			return false;
		}
		if (pid == 0)
		{
			int devNull = open("/dev/null", O_RDWR);
			if (devNull >= 0)
			{
				dup2(devNull, STDIN_FILENO);
				dup2(devNull, STDOUT_FILENO);
				dup2(devNull, STDERR_FILENO);
				if (devNull > 2) close(devNull);
			}
			execlp("curl", "curl", "-fsSL", "--connect-timeout", "20", "--retry", "2",
			       "-A", "yosuga-linux-bootstrap/1.0", "-o", destPath.c_str(), url.c_str(), (char *)nullptr);
			execlp("wget", "wget", "-q", "-T", "30", "-t", "2",
			       "-U", "yosuga-linux-bootstrap/1.0", "-O", destPath.c_str(), url.c_str(), (char *)nullptr);
			_exit(127);
		}
		int status = 0;
		for (;;)
		{
			if (cancelFlag.load())
			{
				kill(pid, SIGTERM);
				waitpid(pid, &status, 0);
				unlink(destPath.c_str());
				outErr = "已取消";
				return false;
			}
			pid_t w = waitpid(pid, &status, WNOHANG);
			if (w == pid) break;
			if (onProgress && *onProgress)
			{
				int64_t cur = FileSizeOf(destPath);
				if (cur > 0) (*onProgress)(cur, expectedSize);
			}
			usleep(80000);
		}
		if (WIFEXITED(status) && WEXITSTATUS(status) == 0 && IsRegularFile(destPath))
		{
			if (onProgress && *onProgress)
			{
				int64_t cur = FileSizeOf(destPath);
				if (cur > 0) (*onProgress)(cur, expectedSize);
			}
			return true;
		}
		if (WIFEXITED(status) && WEXITSTATUS(status) == 127)
			outErr = "未检测到系统 libcurl / curl / wget，请安装 curl 或使用「导入本地文件」";
		else
			outErr = "网络下载失败 (退出码 " + std::to_string(WIFEXITED(status) ? WEXITSTATUS(status) : -1) + ")";
		return false;
	}

	static bool FetchBytesCli(const std::string &url, const std::atomic<bool> &cancelFlag,
	                          std::string &outBody, std::string &outErr)
	{
		char tmpTemplate[] = "/tmp/krkr-manifest-XXXXXX";
		int fd = mkstemp(tmpTemplate);
		if (fd < 0)
		{
			outErr = "无法创建临时文件";
			return false;
		}
		close(fd);
		std::string tmpPath(tmpTemplate);
		bool ok = RunCliDownload(url, tmpPath, 0, cancelFlag, nullptr, outErr);
		if (ok) ok = ReadWholeFile(tmpPath, outBody);
		unlink(tmpPath.c_str());
		return ok;
	}

	static bool DownloadStreamCli(const std::string &url, const std::string &destPath,
	                              int64_t expectedSize, const std::atomic<bool> &cancelFlag,
	                              const ProgressFn &onProgress, std::string &outErr)
	{
		return RunCliDownload(url, destPath, expectedSize, cancelFlag, &onProgress, outErr);
	}

	void *handle_;
	bool ready_;
	GlobalInitFn global_init_ = nullptr;
	EasyInitFn easy_init_ = nullptr;
	EasySetoptFn easy_setopt_ = nullptr;
	EasyPerformFn easy_perform_ = nullptr;
	EasyGetinfoFn easy_getinfo_ = nullptr;
	EasyCleanupFn easy_cleanup_ = nullptr;
	EasyStrerrorFn easy_strerror_ = nullptr;
};

/* =========================================================================
 * PNG Decoder (libpng -> SDL_PIXELFORMAT_ARGB8888)
 * ========================================================================= */

static SDL_Surface *LoadPngSurface(const std::string &path)
{
	if (path.empty()) return nullptr;
	FILE *fp = fopen(path.c_str(), "rb");
	if (!fp) return nullptr;

	uint8_t sig[8];
	if (fread(sig, 1, 8, fp) != 8 || png_sig_cmp(sig, 0, 8) != 0)
	{
		fclose(fp);
		return nullptr;
	}

	png_structp png_ptr = png_create_read_struct(PNG_LIBPNG_VER_STRING, nullptr, nullptr, nullptr);
	if (!png_ptr)
	{
		fclose(fp);
		return nullptr;
	}
	png_infop info_ptr = png_create_info_struct(png_ptr);
	if (!info_ptr)
	{
		png_destroy_read_struct(&png_ptr, nullptr, nullptr);
		fclose(fp);
		return nullptr;
	}

	SDL_Surface *surf = nullptr;
	std::vector<png_bytep> row_ptrs;

	if (setjmp(png_jmpbuf(png_ptr)))
	{
		if (surf) SDL_FreeSurface(surf);
		png_destroy_read_struct(&png_ptr, &info_ptr, nullptr);
		fclose(fp);
		return nullptr;
	}

	png_init_io(png_ptr, fp);
	png_set_sig_bytes(png_ptr, 8);
	png_read_info(png_ptr, info_ptr);

	png_uint_32 width = png_get_image_width(png_ptr, info_ptr);
	png_uint_32 height = png_get_image_height(png_ptr, info_ptr);
	int bit_depth = png_get_bit_depth(png_ptr, info_ptr);
	int color_type = png_get_color_type(png_ptr, info_ptr);

	if (width == 0 || height == 0 || width > 8192 || height > 8192)
	{
		png_destroy_read_struct(&png_ptr, &info_ptr, nullptr);
		fclose(fp);
		return nullptr;
	}

	if (bit_depth == 16)
		png_set_strip_16(png_ptr);
	if (color_type == PNG_COLOR_TYPE_PALETTE)
		png_set_palette_to_rgb(png_ptr);
	if (color_type == PNG_COLOR_TYPE_GRAY && bit_depth < 8)
		png_set_expand_gray_1_2_4_to_8(png_ptr);
	if (png_get_valid(png_ptr, info_ptr, PNG_INFO_tRNS))
		png_set_tRNS_to_alpha(png_ptr);
	if (color_type == PNG_COLOR_TYPE_GRAY || color_type == PNG_COLOR_TYPE_GRAY_ALPHA)
		png_set_gray_to_rgb(png_ptr);
	if ((color_type & PNG_COLOR_MASK_ALPHA) == 0 && !png_get_valid(png_ptr, info_ptr, PNG_INFO_tRNS))
		png_set_add_alpha(png_ptr, 0xFF, PNG_FILLER_AFTER);

	/* Little-endian ARGB8888 stores bytes in memory as B, G, R, A. */
	png_set_bgr(png_ptr);
	png_read_update_info(png_ptr, info_ptr);

	surf = SDL_CreateRGBSurfaceWithFormat(0, (int)width, (int)height, 32, SDL_PIXELFORMAT_ARGB8888);
	if (!surf)
	{
		png_destroy_read_struct(&png_ptr, &info_ptr, nullptr);
		fclose(fp);
		return nullptr;
	}

	row_ptrs.resize(height);
	for (png_uint_32 y = 0; y < height; ++y)
		row_ptrs[y] = (png_bytep)((uint8_t *)surf->pixels + (size_t)y * (size_t)surf->pitch);

	png_read_image(png_ptr, row_ptrs.data());
	png_read_end(png_ptr, nullptr);
	png_destroy_read_struct(&png_ptr, &info_ptr, nullptr);
	fclose(fp);

	SDL_SetSurfaceBlendMode(surf, SDL_BLENDMODE_BLEND);
	return surf;
}

/* =========================================================================
 * FreeType UTF-8 Text Renderer (Host Font + Bundled CJK Fallback)
 * ========================================================================= */

static bool NextUtf8Codepoint(const std::string &s, size_t &i, uint32_t &cp)
{
	if (i >= s.size()) return false;
	uint8_t b0 = (uint8_t)s[i++];
	if ((b0 & 0x80u) == 0)
	{
		cp = b0;
		return true;
	}
	if ((b0 & 0xE0u) == 0xC0u && i < s.size())
	{
		uint8_t b1 = (uint8_t)s[i++];
		cp = ((uint32_t)(b0 & 0x1Fu) << 6) | (uint32_t)(b1 & 0x3Fu);
		return true;
	}
	if ((b0 & 0xF0u) == 0xE0u && i + 1 < s.size())
	{
		uint8_t b1 = (uint8_t)s[i++];
		uint8_t b2 = (uint8_t)s[i++];
		cp = ((uint32_t)(b0 & 0x0Fu) << 12) | ((uint32_t)(b1 & 0x3Fu) << 6) | (uint32_t)(b2 & 0x3Fu);
		return true;
	}
	if ((b0 & 0xF8u) == 0xF0u && i + 2 < s.size())
	{
		uint8_t b1 = (uint8_t)s[i++];
		uint8_t b2 = (uint8_t)s[i++];
		uint8_t b3 = (uint8_t)s[i++];
		cp = ((uint32_t)(b0 & 0x07u) << 18) | ((uint32_t)(b1 & 0x3Fu) << 12) |
		     ((uint32_t)(b2 & 0x3Fu) << 6) | (uint32_t)(b3 & 0x3Fu);
		return true;
	}
	cp = 0xFFFDu;
	return true;
}

static void PopLastUtf8Char(std::string &s)
{
	while (!s.empty())
	{
		uint8_t c = (uint8_t)s.back();
		s.pop_back();
		if ((c & 0xC0u) != 0x80u) break;
	}
}

class FontRenderer {
public:
	FontRenderer() : lib_(nullptr) {}

	~FontRenderer()
	{
		ClearCache();
		for (size_t i = 0; i < faces_.size(); ++i)
		{
			if (faces_[i]) FT_Done_Face(faces_[i]);
		}
		if (lib_) FT_Done_FreeType(lib_);
	}

	bool Init(const std::string &assetDir)
	{
		if (FT_Init_FreeType(&lib_) != 0)
			return false;

		std::vector<std::string> candidates;
		AddFcMatchFont("sans-serif:lang=zh-cn", candidates);
		AddFcMatchFont(":lang=zh", candidates);

		const char *knownPaths[] = {
			"/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc",
			"/usr/share/fonts/noto-cjk/NotoSansCJK-Regular.ttc",
			"/usr/share/fonts/google-noto-cjk/NotoSansCJK-Regular.ttc",
			"/usr/share/fonts/truetype/noto/NotoSansCJK-Regular.ttc",
			"/usr/share/fonts/opentype/noto/NotoSansCJKsc-Regular.otf",
			"/usr/share/fonts/truetype/wqy/wqy-microhei.ttc",
			"/usr/share/fonts/wenquanyi/wqy-microhei/wqy-microhei.ttc",
			"/usr/share/fonts/truetype/wqy/wqy-zenhei.ttc",
			"/usr/share/fonts/truetype/droid/DroidSansFallbackFull.ttf",
			"/usr/share/fonts/adobe-source-han-sans/SourceHanSansCN-Regular.otf",
			"/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
			nullptr
		};
		for (int i = 0; knownPaths[i]; ++i)
			candidates.push_back(knownPaths[i]);

		if (!assetDir.empty())
		{
			candidates.push_back(assetDir + "/fallback.ttc");
			candidates.push_back(assetDir + "/fallback.ttf");
		}
		AddFcMatchFont("sans-serif", candidates);

		std::set<std::string> loaded;
		for (size_t i = 0; i < candidates.size(); ++i)
		{
			const std::string &p = candidates[i];
			if (p.empty() || loaded.count(p) || !IsRegularFile(p))
				continue;
			FT_Face face = nullptr;
			if (FT_New_Face(lib_, p.c_str(), 0, &face) == 0 && face)
			{
				FT_Select_Charmap(face, FT_ENCODING_UNICODE);
				faces_.push_back(face);
				loaded.insert(p);
				if (faces_.size() >= 4) break;
			}
		}
		return !faces_.empty();
	}

	void DrawText(SDL_Surface *dst, const std::string &text, int fontPx,
	              SDL_Color color, const SDL_Rect &box, bool alignCenter)
	{
		if (!dst || text.empty() || faces_.empty() || box.w <= 4 || box.h <= 4)
			return;

		CacheKey key{ text, fontPx, box.w, alignCenter,
		              ((uint32_t)color.a << 24) | ((uint32_t)color.r << 16) |
		              ((uint32_t)color.g << 8) | (uint32_t)color.b };

		SDL_Surface *rendered = nullptr;
		std::map<CacheKey, SDL_Surface *>::iterator it = cache_.find(key);
		if (it != cache_.end())
		{
			rendered = it->second;
		}
		else
		{
			if (cache_.size() >= 48) ClearCache();
			rendered = RasterizeBlock(text, fontPx, color, box.w, alignCenter);
			if (rendered) cache_[key] = rendered;
		}
		if (!rendered) return;

		SDL_Rect dstRect;
		dstRect.x = alignCenter ? (box.x + (box.w - rendered->w) / 2) : box.x;
		dstRect.y = box.y;
		dstRect.w = rendered->w;
		dstRect.h = rendered->h;
		SDL_BlitSurface(rendered, nullptr, dst, &dstRect);
	}

private:
	struct CacheKey {
		std::string text;
		int fontPx;
		int maxWidth;
		bool center;
		uint32_t argb;
		bool operator<(const CacheKey &o) const
		{
			if (fontPx != o.fontPx) return fontPx < o.fontPx;
			if (maxWidth != o.maxWidth) return maxWidth < o.maxWidth;
			if (center != o.center) return center < o.center;
			if (argb != o.argb) return argb < o.argb;
			return text < o.text;
		}
	};

	struct GlyphMetric {
		uint32_t cp;
		FT_Face face;
		int advance;
	};

	static void AddFcMatchFont(const char *pattern, std::vector<std::string> &out)
	{
		std::string cmd = std::string("fc-match -f '%{file}\\n' '") + pattern + "' 2>/dev/null";
		FILE *p = popen(cmd.c_str(), "r");
		if (!p) return;
		char buf[1024];
		if (fgets(buf, sizeof(buf), p))
		{
			std::string path = TrimStr(buf);
			if (!path.empty()) out.push_back(path);
		}
		pclose(p);
	}

	void ClearCache()
	{
		for (std::map<CacheKey, SDL_Surface *>::iterator it = cache_.begin(); it != cache_.end(); ++it)
		{
			if (it->second) SDL_FreeSurface(it->second);
		}
		cache_.clear();
	}

	FT_Face PickFace(uint32_t cp, int fontPx)
	{
		for (size_t i = 0; i < faces_.size(); ++i)
		{
			FT_Set_Pixel_Sizes(faces_[i], 0, (FT_UInt)fontPx);
			if (FT_Get_Char_Index(faces_[i], cp) != 0)
				return faces_[i];
		}
		FT_Set_Pixel_Sizes(faces_[0], 0, (FT_UInt)fontPx);
		return faces_[0];
	}

	SDL_Surface *RasterizeBlock(const std::string &text, int fontPx, SDL_Color color,
	                            int maxWidth, bool alignCenter)
	{
		std::vector<std::vector<GlyphMetric> > lines;
		std::vector<int> lineWidths;
		std::vector<GlyphMetric> curLine;
		int curW = 0;

		size_t idx = 0;
		uint32_t cp = 0;
		while (NextUtf8Codepoint(text, idx, cp))
		{
			if (cp == '\r') continue;
			if (cp == '\n')
			{
				lines.push_back(curLine);
				lineWidths.push_back(curW);
				curLine.clear();
				curW = 0;
				continue;
			}
			FT_Face face = PickFace(cp, fontPx);
			int adv = fontPx / 2;
			if (FT_Load_Char(face, cp, FT_LOAD_DEFAULT) == 0 && face->glyph)
				adv = (int)(face->glyph->advance.x >> 6);
			if (adv <= 0) adv = fontPx / 2;

			if (!curLine.empty() && curW + adv > maxWidth)
			{
				lines.push_back(curLine);
				lineWidths.push_back(curW);
				curLine.clear();
				curW = 0;
			}
			curLine.push_back(GlyphMetric{ cp, face, adv });
			curW += adv;
		}
		if (!curLine.empty() || lines.empty())
		{
			lines.push_back(curLine);
			lineWidths.push_back(curW);
		}

		int lineHeight = (int)std::round(fontPx * 1.38);
		int ascent = (int)std::round(fontPx * 0.88);
		int surfW = std::max(4, maxWidth);
		int surfH = std::max(lineHeight, (int)lines.size() * lineHeight + 6);

		SDL_Surface *surf = SDL_CreateRGBSurfaceWithFormat(0, surfW, surfH, 32, SDL_PIXELFORMAT_ARGB8888);
		if (!surf) return nullptr;
		SDL_SetSurfaceBlendMode(surf, SDL_BLENDMODE_BLEND);
		SDL_FillRect(surf, nullptr, 0x00000000u);

		for (size_t row = 0; row < lines.size(); ++row)
		{
			int penX = alignCenter ? std::max(0, (surfW - lineWidths[row]) / 2) : 0;
			int baselineY = (int)row * lineHeight + ascent;

			for (size_t g = 0; g < lines[row].size(); ++g)
			{
				FT_Face face = lines[row][g].face;
				FT_Set_Pixel_Sizes(face, 0, (FT_UInt)fontPx);
				if (FT_Load_Char(face, lines[row][g].cp, FT_LOAD_RENDER) == 0 && face->glyph)
				{
					const FT_Bitmap &bm = face->glyph->bitmap;
					int gx = penX + face->glyph->bitmap_left;
					int gy = baselineY - face->glyph->bitmap_top;

					for (unsigned int by = 0; by < bm.rows; ++by)
					{
						int py = gy + (int)by;
						if (py < 0 || py >= surfH) continue;
						uint32_t *dstRow = (uint32_t *)((uint8_t *)surf->pixels + py * surf->pitch);
						const uint8_t *srcRow = bm.buffer + (int)by * bm.pitch;

						for (unsigned int bx = 0; bx < bm.width; ++bx)
						{
							int px = gx + (int)bx;
							if (px < 0 || px >= surfW) continue;
							uint8_t cov = 0;
							if (bm.pixel_mode == FT_PIXEL_MODE_GRAY)
								cov = srcRow[bx];
							else if (bm.pixel_mode == FT_PIXEL_MODE_MONO)
								cov = (srcRow[bx >> 3] & (0x80u >> (bx & 7u))) ? 255u : 0u;
							if (cov == 0) continue;

							uint32_t alpha = ((uint32_t)cov * (uint32_t)color.a) / 255u;
							uint32_t exist = dstRow[px];
							uint32_t existA = (exist >> 24) & 0xFFu;
							if (alpha > existA)
							{
								dstRow[px] = (alpha << 24) |
								             ((uint32_t)color.r << 16) |
								             ((uint32_t)color.g << 8) |
								             (uint32_t)color.b;
							}
						}
					}
				}
				penX += lines[row][g].advance;
			}
		}
		return surf;
	}

	FT_Library lib_;
	std::vector<FT_Face> faces_;
	std::map<CacheKey, SDL_Surface *> cache_;
};

/* =========================================================================
 * Native Desktop File Picker Helper (zenity / kdialog / yad)
 * ========================================================================= */

static bool HasExecutableInPath(const char *prog)
{
	const char *pathEnv = getenv("PATH");
	if (!pathEnv || !prog || !prog[0]) return false;
	std::string paths(pathEnv);
	size_t start = 0;
	while (start <= paths.size())
	{
		size_t colon = paths.find(':', start);
		std::string dir = colon == std::string::npos ? paths.substr(start) : paths.substr(start, colon - start);
		if (!dir.empty())
		{
			std::string full = dir + "/" + prog;
			if (access(full.c_str(), X_OK) == 0 && IsRegularFile(full))
				return true;
		}
		if (colon == std::string::npos) break;
		start = colon + 1;
	}
	return false;
}

static bool OpenSystemFilePicker(std::vector<std::string> &outPaths, bool &pickerAvailable)
{
	outPaths.clear();
	std::string cmd;
	if (HasExecutableInPath("zenity"))
	{
		cmd = "zenity --file-selection --multiple --separator='\n' "
		      "--title='选择游戏数据包 (.zip 分包或 data.xp3)' "
		      "--file-filter='Game Data (*.zip *.xp3) | *.zip *.ZIP *.xp3 *.XP3' "
		      "--file-filter='All files | *' 2>/dev/null";
	}
	else if (HasExecutableInPath("kdialog"))
	{
		const char *home = getenv("HOME");
		std::string startDir = (home && home[0]) ? home : ".";
		cmd = "kdialog --multiple --separate-output --title '选择游戏数据包' --getopenfilename '" +
		      startDir + "' '*.zip *.ZIP *.xp3 *.XP3|Game Data (*.zip, *.xp3)' 2>/dev/null";
	}
	else if (HasExecutableInPath("yad"))
	{
		cmd = "yad --file --multiple --separator='\n' --title='选择游戏数据包 (.zip 分包或 data.xp3)' 2>/dev/null";
	}
	else
	{
		pickerAvailable = false;
		return false;
	}

	pickerAvailable = true;
	FILE *p = popen(cmd.c_str(), "r");
	if (!p) return false;
	char line[4096];
	while (fgets(line, sizeof(line), p))
	{
		std::string s = TrimStr(line);
		if (!s.empty()) outPaths.push_back(s);
	}
	int rc = pclose(p);
	return WIFEXITED(rc) && WEXITSTATUS(rc) == 0 && !outPaths.empty();
}

static void ExpandInputPathList(const std::vector<std::string> &rawInputs,
                                std::vector<std::string> &outFiles)
{
	outFiles.clear();
	for (size_t i = 0; i < rawInputs.size(); ++i)
	{
		std::string p = TrimStr(rawInputs[i]);
		if (p.size() >= 2 && ((p.front() == '"' && p.back() == '"') || (p.front() == '\'' && p.back() == '\'')))
			p = p.substr(1, p.size() - 2);
		if (p.compare(0, 7, "file://") == 0)
			p = p.substr(7);
		if (p.size() >= 2 && p[0] == '~' && p[1] == '/')
		{
			const char *home = getenv("HOME");
			if (home && home[0]) p = std::string(home) + p.substr(1);
		}
		if (IsDirectory(p))
		{
			if (IsRegularFile(p + "/data.xp3"))
			{
				outFiles.push_back(p + "/data.xp3");
				continue;
			}
			DIR *d = opendir(p.c_str());
			if (d)
			{
				std::vector<std::string> dirZips;
				struct dirent *ent;
				while ((ent = readdir(d)) != nullptr)
				{
					std::string name(ent->d_name);
					if (EndsWithNoCase(name, ".zip") || EndsWithNoCase(name, ".xp3"))
						dirZips.push_back(p + "/" + name);
				}
				closedir(d);
				std::sort(dirZips.begin(), dirZips.end());
				outFiles.insert(outFiles.end(), dirZips.begin(), dirZips.end());
			}
		}
		else if (IsRegularFile(p))
		{
			outFiles.push_back(p);
		}
	}
}

/* =========================================================================
 * Official 1920x1080 Bootstrap Window & State Machine
 * ========================================================================= */

struct DataAssetItem {
	std::string name;
	int64_t size = 0;
	std::string sha256;
	int fileCount = 0;
};

class BootstrapWindow {
public:
	BootstrapWindow(const std::string &appRoot, const std::string &assetDir)
		: appRoot_(appRoot)
		, assetDir_(assetDir)
		, window_(nullptr)
		, canvas_(nullptr)
		, cancelFlag_(false)
		, readyToStart_(false)
		, busy_(false)
		, selectedProxy_(1)
		, activeAction_(0)
		, hoverProxy_(0)
		, hoverAction_(0)
		, progress_(0.0)
		, extractProgress_(0.0)
		, extractVisible_(false)
		, modalMode_(kModalNone)
		, modalFocusField_(0)
		, downloadMouseDownTick_(0)
		, downloadLongPressTriggered_(false)
	{
		LoadDefaults();
	}

	~BootstrapWindow()
	{
		cancelFlag_.store(true);
		JoinWorker();
		FreeArt();
		if (canvas_) SDL_FreeSurface(canvas_);
		if (window_) SDL_DestroyWindow(window_);
	}

	bool Run()
	{
		if (!SDL_WasInit(SDL_INIT_VIDEO))
		{
			if (SDL_Init(SDL_INIT_VIDEO | SDL_INIT_EVENTS | SDL_INIT_TIMER) < 0)
			{
				fprintf(stderr, "[Bootstrap] SDL_Init failed: %s\n", SDL_GetError());
				return false;
			}
		}

		SDL_EventState(SDL_DROPFILE, SDL_ENABLE);

		int initW = 1280;
		int initH = 720;
		SDL_DisplayMode dm;
		if (SDL_GetDesktopDisplayMode(0, &dm) == 0 && dm.w >= 1920 && dm.h >= 1200)
		{
			initW = 1600;
			initH = 900;
		}

		window_ = SDL_CreateWindow(
			"缘之空：高清重制",
			SDL_WINDOWPOS_CENTERED, SDL_WINDOWPOS_CENTERED,
			initW, initH,
			SDL_WINDOW_SHOWN | SDL_WINDOW_RESIZABLE | SDL_WINDOW_ALLOW_HIGHDPI);
		if (!window_)
		{
			fprintf(stderr, "[Bootstrap] SDL_CreateWindow failed: %s\n", SDL_GetError());
			return false;
		}
		SDL_SetWindowMinimumSize(window_, 800, 450);

		canvas_ = SDL_CreateRGBSurfaceWithFormat(0, kDesignW, kDesignH, 32, SDL_PIXELFORMAT_ARGB8888);
		if (!canvas_) return false;

		font_.Init(assetDir_);
		LoadArt();
		if (artIcon_)
			SDL_SetWindowIcon(window_, artIcon_);

		ProbeExistingState();

		bool quitRequested = false;
		uint32_t lastRenderTick = 0;

		while (!quitRequested)
		{
			if (readyToStart_.load())
				break;

			SDL_Event ev;
			while (SDL_PollEvent(&ev))
			{
				if (ev.type == SDL_QUIT)
				{
					quitRequested = true;
					break;
				}
				HandleEvent(ev);
			}
			if (quitRequested || readyToStart_.load())
				break;

			/* Long-press (>= 600 ms) on Download button opens custom URL dialog,
			 * matching IOSBootstrap.mm / BootstrapActivity.java. */
			if (downloadMouseDownTick_ != 0 && !downloadLongPressTriggered_ &&
			    !busy_.load() && modalMode_ == kModalNone)
			{
				if (SDL_GetTicks() - downloadMouseDownTick_ >= 600)
				{
					downloadLongPressTriggered_ = true;
					OpenCustomSourceModal();
				}
			}

			uint32_t now = SDL_GetTicks();
			if (now - lastRenderTick >= 33)
			{
				RenderFrame();
				lastRenderTick = now;
			}
			SDL_Delay(12);
		}

		if (readyToStart_.load())
		{
			JoinWorker();
			if (modalMode_ != kModalNone)
				SDL_StopTextInput();
			if (window_)
			{
				SDL_DestroyWindow(window_);
				window_ = nullptr;
			}
			SDL_FlushEvents(SDL_FIRSTEVENT, SDL_LASTEVENT);
			return true;
		}

		cancelFlag_.store(true);
		JoinWorker();
		if (modalMode_ != kModalNone)
			SDL_StopTextInput();
		if (window_)
		{
			SDL_DestroyWindow(window_);
			window_ = nullptr;
		}
		SDL_Quit();
		return false;
	}

private:
	enum ModalMode {
		kModalNone = 0,
		kModalCustomUrl = 1,
		kModalImportPath = 2
	};

	void JoinWorker()
	{
		if (worker_.joinable())
			worker_.join();
	}

	void LoadDefaults()
	{
		defaultRepo_ = KRKRSDL2_DEFAULT_DATA_REPO;
		defaultBaseUrl_ = "https://github.com/" + defaultRepo_ + "/releases/latest/download/";

		if (!assetDir_.empty())
		{
			std::string text;
			if (ReadWholeFile(assetDir_ + "/default-manifest.json", text))
			{
				JsonVal v;
				if (ParseJson(text, v) && v.type == JsonVal::kObject)
				{
					std::string u = TrimStr(v.GetStr("baseUrl"));
					if (!u.empty())
					{
						defaultBaseUrl_ = u;
						size_t ghPos = u.find("github.com/");
						if (ghPos != std::string::npos)
						{
							std::string rest = u.substr(ghPos + 11);
							size_t s1 = rest.find('/');
							size_t s2 = s1 == std::string::npos ? std::string::npos : rest.find('/', s1 + 1);
							if (s1 != std::string::npos && s2 != std::string::npos)
								defaultRepo_ = rest.substr(0, s2);
						}
					}
				}
			}
		}

		std::string prefsText;
		if (ReadWholeFile(appRoot_ + "/bootstrap-prefs.json", prefsText))
		{
			JsonVal v;
			if (ParseJson(prefsText, v) && v.type == JsonVal::kObject)
			{
				customBaseUrl_ = TrimStr(v.GetStr("customBaseUrl"));
				customProxy_ = TrimStr(v.GetStr("customProxy"));
				int p = (int)v.GetInt64("selectedProxy", 1);
				if (p >= 1 && p <= 3) selectedProxy_ = p;
			}
		}
	}

	void SavePrefs()
	{
		auto esc = [](const std::string &s) -> std::string {
			std::string out;
			for (size_t i = 0; i < s.size(); ++i)
			{
				if (s[i] == '"' || s[i] == '\\') out.push_back('\\');
				out.push_back(s[i]);
			}
			return out;
		};
		std::string json = "{\"selectedProxy\":" + std::to_string(selectedProxy_) +
		                   ",\"customBaseUrl\":\"" + esc(customBaseUrl_) +
		                   "\",\"customProxy\":\"" + esc(customProxy_) + "\"}\n";
		WriteWholeFile(appRoot_ + "/bootstrap-prefs.json", json);
	}

	void LoadArt()
	{
		auto load = [&](const char *name) -> SDL_Surface * {
			if (assetDir_.empty()) return nullptr;
			return LoadPngSurface(assetDir_ + "/" + name);
		};
		artBg_ = load("Background.png");
		artDirect_ = load("github_direct.png");
		artDirectSel_ = load("github_direct_selected.png");
		artGh_ = load("gh_proxy_label.png");
		artGhSel_ = load("gh_proxy_label_selected.png");
		artCraft_ = load("craft_hello_label.png");
		artCraftSel_ = load("craft_hello_label_selected.png");
		artTrack_ = load("progress_track.png");
		artDownload_ = load("download_label.png");
		artDownloadAct_ = load("download_label_active.png");
		artImport_ = load("import_label.png");
		artImportAct_ = load("import_label_active.png");
		artIcon_ = load("icon.png");
	}

	void FreeArt()
	{
		SDL_Surface **surfs[] = {
			&artBg_, &artDirect_, &artDirectSel_, &artGh_, &artGhSel_,
			&artCraft_, &artCraftSel_, &artTrack_, &artDownload_,
			&artDownloadAct_, &artImport_, &artImportAct_, &artIcon_
		};
		for (size_t i = 0; i < sizeof(surfs) / sizeof(surfs[0]); ++i)
		{
			if (*surfs[i]) { SDL_FreeSurface(*surfs[i]); *surfs[i] = nullptr; }
		}
	}

	void ProbeExistingState()
	{
		std::vector<int> missing = MissingPackIndices(appRoot_, 0);
		if (!missing.empty())
		{
			SetUiStatus("已检测到未完成的分包导入，还缺：" + FormatPackIndexList(missing) +
			            " — 请继续点击「导入本地文件」补齐，或点击「开始下载」自动获取完整资源", "");
		}
		else
		{
			SetUiStatus("未检测到游戏资源，点击按钮开始下载或导入本地文件", "");
		}
	}

	void SetUiStatus(const std::string &progressMsg, const std::string &errMsg)
	{
		std::lock_guard<std::mutex> lk(uiMutex_);
		progressText_ = progressMsg;
		errorText_ = errMsg;
	}

	void SetDownloadProgress(double ratio, const std::string &text)
	{
		std::lock_guard<std::mutex> lk(uiMutex_);
		progress_ = std::max(0.0, std::min(1.0, ratio));
		progressText_ = text;
	}

	void SetExtractProgress(bool visible, double ratio, const std::string &text)
	{
		std::lock_guard<std::mutex> lk(uiMutex_);
		extractVisible_ = visible;
		extractProgress_ = std::max(0.0, std::min(1.0, ratio));
		extractText_ = text;
	}

	SDL_Rect ComputeLetterbox(int winW, int winH) const
	{
		double sx = (double)winW / (double)kDesignW;
		double sy = (double)winH / (double)kDesignH;
		double scale = std::min(sx, sy);
		int dstW = std::max(1, (int)std::round(kDesignW * scale));
		int dstH = std::max(1, (int)std::round(kDesignH * scale));
		SDL_Rect r{ (winW - dstW) / 2, (winH - dstH) / 2, dstW, dstH };
		return r;
	}

	bool WindowToDesign(int wx, int wy, int &dx, int &dy) const
	{
		if (!window_) return false;
		int winW = 1, winH = 1;
		SDL_GetWindowSize(window_, &winW, &winH);
		SDL_Rect lb = ComputeLetterbox(winW, winH);
		dx = (int)std::round((double)(wx - lb.x) * (double)kDesignW / (double)lb.w);
		dy = (int)std::round((double)(wy - lb.y) * (double)kDesignH / (double)lb.h);
		return dx >= 0 && dx < kDesignW && dy >= 0 && dy < kDesignH;
	}

	static bool InRect(int x, int y, const SDL_Rect &r)
	{
		return x >= r.x && x < r.x + r.w && y >= r.y && y < r.y + r.h;
	}

	static void FillRectArgb(SDL_Surface *s, const SDL_Rect &r, uint32_t argb)
	{
		SDL_Rect clip = r;
		if (clip.x < 0) { clip.w += clip.x; clip.x = 0; }
		if (clip.y < 0) { clip.h += clip.y; clip.y = 0; }
		if (clip.x + clip.w > s->w) clip.w = s->w - clip.x;
		if (clip.y + clip.h > s->h) clip.h = s->h - clip.y;
		if (clip.w <= 0 || clip.h <= 0) return;

		uint32_t a = (argb >> 24) & 0xFFu;
		if (a == 255u)
		{
			SDL_FillRect(s, &clip, argb);
			return;
		}
		uint32_t sr = (argb >> 16) & 0xFFu;
		uint32_t sg = (argb >> 8) & 0xFFu;
		uint32_t sb = argb & 0xFFu;
		uint32_t invA = 255u - a;
		for (int y = clip.y; y < clip.y + clip.h; ++y)
		{
			uint32_t *row = (uint32_t *)((uint8_t *)s->pixels + y * s->pitch);
			for (int x = clip.x; x < clip.x + clip.w; ++x)
			{
				uint32_t d = row[x];
				uint32_t dr = ((d >> 16) & 0xFFu) * invA + sr * a;
				uint32_t dg = ((d >> 8) & 0xFFu) * invA + sg * a;
				uint32_t db = (d & 0xFFu) * invA + sb * a;
				row[x] = 0xFF000000u | ((dr / 255u) << 16) | ((dg / 255u) << 8) | (db / 255u);
			}
		}
	}

	static void StrokeRectArgb(SDL_Surface *s, const SDL_Rect &r, int border, uint32_t argb)
	{
		FillRectArgb(s, SDL_Rect{ r.x, r.y, r.w, border }, argb);
		FillRectArgb(s, SDL_Rect{ r.x, r.y + r.h - border, r.w, border }, argb);
		FillRectArgb(s, SDL_Rect{ r.x, r.y, border, r.h }, argb);
		FillRectArgb(s, SDL_Rect{ r.x + r.w - border, r.y, border, r.h }, argb);
	}

	static void BlitArt(SDL_Surface *dst, SDL_Surface *art, const SDL_Rect &r)
	{
		if (!art) return;
		SDL_Rect target = r;
		if (art->w == r.w && art->h == r.h)
			SDL_BlitSurface(art, nullptr, dst, &target);
		else
			SDL_BlitScaled(art, nullptr, dst, &target);
	}

	void RenderFrame()
	{
		if (!window_ || !canvas_) return;

		/* 1. Background (1920x1080) */
		if (artBg_)
		{
			SDL_Rect full{ 0, 0, kDesignW, kDesignH };
			BlitArt(canvas_, artBg_, full);
		}
		else
		{
			SDL_FillRect(canvas_, nullptr, 0xFFF4F7FBu);
			font_.DrawText(canvas_, "缘之空：高清重制", 54,
			               SDL_Color{ 35, 52, 84, 255 }, SDL_Rect{ 200, 220, 1520, 80 }, true);
		}

		bool isBusy = busy_.load();
		int act = activeAction_.load();

		/* 2. Proxy selector artwork (exact IOSBootstrap coordinates) */
		bool p1On = (selectedProxy_ == 1 || hoverProxy_ == 1) && customProxy_.empty();
		bool p2On = (selectedProxy_ == 2 || hoverProxy_ == 2) && customProxy_.empty();
		bool p3On = (selectedProxy_ == 3 || hoverProxy_ == 3) && customProxy_.empty();

		SDL_Rect rDirectImg{ 200, 430, 356, 123 };
		SDL_Rect rGhImg{ 600, 440, 338, 105 };
		SDL_Rect rCraftImg{ 1000, 440, 673, 105 };

		if (artDirect_ || artDirectSel_)
			BlitArt(canvas_, p1On ? (artDirectSel_ ? artDirectSel_ : artDirect_) : artDirect_, rDirectImg);
		else
		{
			FillRectArgb(canvas_, rDirectImg, p1On ? 0xFF1783FFu : 0xFFE3EAF4u);
			font_.DrawText(canvas_, "GitHub 直连", 30, p1On ? SDL_Color{255,255,255,255} : SDL_Color{38,51,77,255},
			               SDL_Rect{ 200, 470, 356, 50 }, true);
		}

		if (artGh_ || artGhSel_)
			BlitArt(canvas_, p2On ? (artGhSel_ ? artGhSel_ : artGh_) : artGh_, rGhImg);
		else
		{
			FillRectArgb(canvas_, rGhImg, p2On ? 0xFF1783FFu : 0xFFE3EAF4u);
			font_.DrawText(canvas_, "gh-proxy 加速", 30, p2On ? SDL_Color{255,255,255,255} : SDL_Color{38,51,77,255},
			               SDL_Rect{ 600, 470, 338, 50 }, true);
		}

		if (artCraft_ || artCraftSel_)
			BlitArt(canvas_, p3On ? (artCraftSel_ ? artCraftSel_ : artCraft_) : artCraft_, rCraftImg);
		else
		{
			FillRectArgb(canvas_, rCraftImg, p3On ? 0xFF1783FFu : 0xFFE3EAF4u);
			font_.DrawText(canvas_, "craft-hello 加速", 30, p3On ? SDL_Color{255,255,255,255} : SDL_Color{38,51,77,255},
			               SDL_Rect{ 1000, 470, 673, 50 }, true);
		}

		/* 3. Action buttons (hidden while transfer is running, matching IOSBootstrap) */
		if (!isBusy)
		{
			bool dlOn = (act == 1 || hoverAction_ == 1);
			bool imOn = (act == 2 || hoverAction_ == 2);
			SDL_Rect rDlImg{ 1270, 800, 136, 57 };
			SDL_Rect rImImg{ 1470, 800, 201, 57 };

			if (artDownload_ || artDownloadAct_)
				BlitArt(canvas_, dlOn ? (artDownloadAct_ ? artDownloadAct_ : artDownload_) : artDownload_, rDlImg);
			else
			{
				FillRectArgb(canvas_, rDlImg, dlOn ? 0xFF1783FFu : 0xFF2B4C7Eu);
				font_.DrawText(canvas_, "开始下载", 28, SDL_Color{255,255,255,255}, SDL_Rect{ 1270, 810, 136, 40 }, true);
			}

			if (artImport_ || artImportAct_)
				BlitArt(canvas_, imOn ? (artImportAct_ ? artImportAct_ : artImport_) : artImport_, rImImg);
			else
			{
				FillRectArgb(canvas_, rImImg, imOn ? 0xFF1783FFu : 0xFF2B4C7Eu);
				font_.DrawText(canvas_, "导入本地文件", 28, SDL_Color{255,255,255,255}, SDL_Rect{ 1470, 810, 201, 40 }, true);
			}
		}

		/* Snapshot dynamic UI strings & progress values */
		double dlProg = 0.0;
		double exProg = 0.0;
		bool exVis = false;
		std::string dlText, exText, errText;
		{
			std::lock_guard<std::mutex> lk(uiMutex_);
			dlProg = progress_;
			exProg = extractProgress_;
			exVis = extractVisible_;
			dlText = progressText_;
			exText = extractText_;
			errText = errorText_;
		}

		/* 4. Error message label (200, 580, 1520, 100) */
		if (!errText.empty())
		{
			font_.DrawText(canvas_, errText, 26,
			               SDL_Color{ 204, 31, 31, 255 }, SDL_Rect{ 200, 576, 1520, 96 }, true);
		}

		/* 5. Extract (secondary green) progress bar */
		if (exVis)
		{
			if (!exText.empty())
			{
				font_.DrawText(canvas_, exText, 26,
				               SDL_Color{ 56, 142, 60, 255 }, SDL_Rect{ 210, 622, 1215, 44 }, true);
			}
			SDL_Rect exTrack{ 210, 668, 1215, 18 };
			if (artTrack_)
				BlitArt(canvas_, artTrack_, exTrack);
			else
				FillRectArgb(canvas_, exTrack, 0xFFD8E0EAu);
			int fillW = (int)std::round(1207.0 * exProg);
			if (fillW > 0)
				FillRectArgb(canvas_, SDL_Rect{ 214, 672, fillW, 10 }, 0xFF4CAF50u);
		}

		/* 6. Download (primary blue) progress bar & status label */
		if (isBusy)
		{
			SDL_Rect dlTrack{ 210, 690, 1215, 26 };
			if (artTrack_)
				BlitArt(canvas_, artTrack_, dlTrack);
			else
				FillRectArgb(canvas_, dlTrack, 0xFFD8E0EAu);
			int fillW = (int)std::round(1207.0 * dlProg);
			if (fillW > 0)
				FillRectArgb(canvas_, SDL_Rect{ 214, 694, fillW, 18 }, 0xFF1783FFu);
		}

		if (!dlText.empty())
		{
			font_.DrawText(canvas_, dlText, 28,
			               SDL_Color{ 38, 51, 77, 255 }, SDL_Rect{ 235, 720, 1450, 80 }, true);
		}

		if (!isBusy && (!customBaseUrl_.empty() || !customProxy_.empty()))
		{
			std::string badge = "已启用自定义下载配置（右键「开始下载」可修改或清空）";
			font_.DrawText(canvas_, badge, 22,
			               SDL_Color{ 23, 131, 255, 230 }, SDL_Rect{ 235, 868, 1450, 36 }, true);
		}

		/* 7. Modal dialog overlay (Custom URL / Local Path input) */
		if (modalMode_ != kModalNone)
			RenderModal();

		/* 8. Present 1920x1080 canvas uniformly scaled into window surface */
		SDL_Surface *winSurf = SDL_GetWindowSurface(window_);
		if (winSurf)
		{
			SDL_Rect lb = ComputeLetterbox(winSurf->w, winSurf->h);
			if (lb.x > 0 || lb.y > 0)
				SDL_FillRect(winSurf, nullptr, 0xFF000000u);
			SDL_BlitScaled(canvas_, nullptr, winSurf, &lb);
			SDL_UpdateWindowSurface(window_);
		}
	}

	void RenderModal()
	{
		FillRectArgb(canvas_, SDL_Rect{ 0, 0, kDesignW, kDesignH }, 0x99101824u);
		SDL_Rect card{ 360, 250, 1200, 560 };
		FillRectArgb(canvas_, card, 0xFFFBFDFEu);
		StrokeRectArgb(canvas_, card, 3, 0xFF1783FFu);

		bool blink = ((SDL_GetTicks() / 500) % 2) == 0;

		if (modalMode_ == kModalCustomUrl)
		{
			font_.DrawText(canvas_, "自定义下载源", 34,
			               SDL_Color{ 24, 36, 56, 255 }, SDL_Rect{ 400, 282, 1120, 48 }, true);
			font_.DrawText(canvas_,
			               "留空使用内置地址；可粘贴完整 data-assets.json 链接或所在目录 URL（Ctrl+V 粘贴，Ctrl+U 清空）",
			               23, SDL_Color{ 92, 106, 128, 255 }, SDL_Rect{ 400, 336, 1120, 40 }, true);

			font_.DrawText(canvas_, "资源地址 (Base URL)：", 24,
			               SDL_Color{ 38, 51, 77, 255 }, SDL_Rect{ 420, 396, 1080, 34 }, false);
			SDL_Rect box1{ 420, 434, 1080, 58 };
			FillRectArgb(canvas_, box1, 0xFFF2F6FAu);
			StrokeRectArgb(canvas_, box1, modalFocusField_ == 0 ? 3 : 2,
			               modalFocusField_ == 0 ? 0xFF1783FFu : 0xFFC5D1DFu);
			std::string f1 = modalField1_.empty() && modalFocusField_ != 0
				? ("默认: " + defaultBaseUrl_)
				: (modalField1_ + (modalFocusField_ == 0 && blink ? "|" : ""));
			font_.DrawText(canvas_, f1, 24,
			               modalField1_.empty() && modalFocusField_ != 0
			                 ? SDL_Color{ 140, 152, 170, 255 }
			                 : SDL_Color{ 24, 36, 56, 255 },
			               SDL_Rect{ 436, 448, 1048, 36 }, false);

			font_.DrawText(canvas_, "自定义代理前缀（可选，填写后覆盖上方预设按钮）：", 24,
			               SDL_Color{ 38, 51, 77, 255 }, SDL_Rect{ 420, 516, 1080, 34 }, false);
			SDL_Rect box2{ 420, 554, 1080, 58 };
			FillRectArgb(canvas_, box2, 0xFFF2F6FAu);
			StrokeRectArgb(canvas_, box2, modalFocusField_ == 1 ? 3 : 2,
			               modalFocusField_ == 1 ? 0xFF1783FFu : 0xFFC5D1DFu);
			std::string f2 = modalField2_.empty() && modalFocusField_ != 1
				? "可选，例如 https://gh-proxy.cn/"
				: (modalField2_ + (modalFocusField_ == 1 && blink ? "|" : ""));
			font_.DrawText(canvas_, f2, 24,
			               modalField2_.empty() && modalFocusField_ != 1
			                 ? SDL_Color{ 140, 152, 170, 255 }
			                 : SDL_Color{ 24, 36, 56, 255 },
			               SDL_Rect{ 436, 568, 1048, 36 }, false);
		}
		else if (modalMode_ == kModalImportPath)
		{
			font_.DrawText(canvas_, "导入本地数据包", 34,
			               SDL_Color{ 24, 36, 56, 255 }, SDL_Rect{ 400, 290, 1120, 48 }, true);
			font_.DrawText(canvas_,
			               "可直接把 .zip 分包或 data.xp3 拖入窗口，或在下方输入文件 / 所在文件夹路径（支持 Ctrl+V 粘贴）：",
			               24, SDL_Color{ 92, 106, 128, 255 }, SDL_Rect{ 410, 355, 1100, 70 }, true);

			SDL_Rect box1{ 420, 455, 1080, 64 };
			FillRectArgb(canvas_, box1, 0xFFF2F6FAu);
			StrokeRectArgb(canvas_, box1, 3, 0xFF1783FFu);
			std::string f1 = modalField1_ + (blink ? "|" : "");
			font_.DrawText(canvas_, f1, 25,
			               SDL_Color{ 24, 36, 56, 255 }, SDL_Rect{ 436, 471, 1048, 38 }, false);
		}

		SDL_Rect btnCancel{ 1020, 700, 210, 64 };
		SDL_Rect btnOk{ 1260, 700, 240, 64 };
		FillRectArgb(canvas_, btnCancel, 0xFFE6ECF3u);
		FillRectArgb(canvas_, btnOk, 0xFF1783FFu);
		font_.DrawText(canvas_, "取消 (Esc)", 26, SDL_Color{ 48, 62, 84, 255 },
		               SDL_Rect{ btnCancel.x, btnCancel.y + 15, btnCancel.w, 36 }, true);
		font_.DrawText(canvas_, modalMode_ == kModalCustomUrl ? "确定并下载" : "开始导入",
		               26, SDL_Color{ 255, 255, 255, 255 },
		               SDL_Rect{ btnOk.x, btnOk.y + 15, btnOk.w, 36 }, true);
	}

	void OpenCustomSourceModal()
	{
		modalMode_ = kModalCustomUrl;
		modalFocusField_ = 0;
		modalField1_ = customBaseUrl_;
		modalField2_ = customProxy_;
		SDL_StartTextInput();
	}

	void OpenImportPathModal()
	{
		modalMode_ = kModalImportPath;
		modalFocusField_ = 0;
		const char *home = getenv("HOME");
		std::string dlDir = (home && home[0]) ? (std::string(home) + "/Downloads") : "";
		modalField1_ = (!dlDir.empty() && IsDirectory(dlDir)) ? dlDir : "";
		SDL_StartTextInput();
	}

	void CloseModal()
	{
		modalMode_ = kModalNone;
		SDL_StopTextInput();
	}

	void ConfirmModal()
	{
		ModalMode mode = modalMode_;
		CloseModal();
		if (mode == kModalCustomUrl)
		{
			customBaseUrl_ = TrimStr(modalField1_);
			customProxy_ = TrimStr(modalField2_);
			SavePrefs();
			StartDownload();
		}
		else if (mode == kModalImportPath)
		{
			std::string path = TrimStr(modalField1_);
			if (!path.empty())
			{
				std::vector<std::string> files;
				ExpandInputPathList({ path }, files);
				if (files.empty())
				{
					SetUiStatus("准备就绪", "未在该路径找到 .zip 分包或 data.xp3: " + path);
				}
				else
				{
					StartImportFiles(files);
				}
			}
		}
	}

	void HandleEvent(const SDL_Event &ev)
	{
		if (ev.type == SDL_USEREVENT && ev.user.code == 1001)
		{
			if (!busy_.load() && modalMode_ == kModalNone)
				OpenImportPathModal();
			return;
		}
		if (ev.type == SDL_DROPFILE)
		{
			if (ev.drop.file)
			{
				if (!busy_.load())
					pendingDrops_.push_back(std::string(ev.drop.file));
				SDL_free(ev.drop.file);
			}
			return;
		}
		if (ev.type == SDL_DROPCOMPLETE)
		{
			if (!busy_.load() && !pendingDrops_.empty())
			{
				if (modalMode_ != kModalNone) CloseModal();
				std::vector<std::string> files;
				ExpandInputPathList(pendingDrops_, files);
				pendingDrops_.clear();
				if (!files.empty())
					StartImportFiles(files);
				else
					SetUiStatus("准备就绪", "拖入的路径中未找到 .zip 或 data.xp3 文件");
			}
			pendingDrops_.clear();
			return;
		}

		if (modalMode_ != kModalNone)
		{
			HandleModalEvent(ev);
			return;
		}

		if (ev.type == SDL_KEYDOWN && !busy_.load())
		{
			if (ev.key.keysym.sym == SDLK_F2)
			{
				OpenCustomSourceModal();
				return;
			}
		}

		SDL_Rect hitDirect{ 20, 425, 550, 145 };
		SDL_Rect hitGh{ 570, 425, 410, 145 };
		SDL_Rect hitCraft{ 980, 425, 740, 145 };
		SDL_Rect hitDownload{ 1240, 755, 300, 135 };
		SDL_Rect hitImport{ 1450, 755, 430, 135 };

		if (ev.type == SDL_MOUSEMOTION)
		{
			int dx = 0, dy = 0;
			hoverProxy_ = 0;
			hoverAction_ = 0;
			if (WindowToDesign(ev.motion.x, ev.motion.y, dx, dy))
			{
				if (InRect(dx, dy, hitDirect)) hoverProxy_ = 1;
				else if (InRect(dx, dy, hitGh)) hoverProxy_ = 2;
				else if (InRect(dx, dy, hitCraft)) hoverProxy_ = 3;

				if (!busy_.load())
				{
					if (InRect(dx, dy, hitDownload)) hoverAction_ = 1;
					else if (InRect(dx, dy, hitImport)) hoverAction_ = 2;
				}
			}
			return;
		}

		if (ev.type == SDL_MOUSEBUTTONDOWN && !busy_.load())
		{
			int dx = 0, dy = 0;
			if (!WindowToDesign(ev.button.x, ev.button.y, dx, dy))
				return;

			if (ev.button.button == SDL_BUTTON_RIGHT && InRect(dx, dy, hitDownload))
			{
				OpenCustomSourceModal();
				return;
			}
			if (ev.button.button == SDL_BUTTON_LEFT)
			{
				if (InRect(dx, dy, hitDirect))
				{
					selectedProxy_ = 1;
					customProxy_.clear();
					SavePrefs();
				}
				else if (InRect(dx, dy, hitGh))
				{
					selectedProxy_ = 2;
					customProxy_.clear();
					SavePrefs();
				}
				else if (InRect(dx, dy, hitCraft))
				{
					selectedProxy_ = 3;
					customProxy_.clear();
					SavePrefs();
				}
				else if (InRect(dx, dy, hitDownload))
				{
					downloadMouseDownTick_ = SDL_GetTicks();
					downloadLongPressTriggered_ = false;
				}
				else if (InRect(dx, dy, hitImport))
				{
					StartPickerAndImport();
				}
			}
			return;
		}

		if (ev.type == SDL_MOUSEBUTTONUP && ev.button.button == SDL_BUTTON_LEFT)
		{
			bool wasTrackingDownload = (downloadMouseDownTick_ != 0);
			bool wasLongPress = downloadLongPressTriggered_;
			downloadMouseDownTick_ = 0;
			downloadLongPressTriggered_ = false;

			if (wasTrackingDownload && !wasLongPress && !busy_.load())
			{
				int dx = 0, dy = 0;
				if (WindowToDesign(ev.button.x, ev.button.y, dx, dy) && InRect(dx, dy, hitDownload))
					StartDownload();
			}
		}
	}

	void HandleModalEvent(const SDL_Event &ev)
	{
		std::string &activeField = (modalMode_ == kModalCustomUrl && modalFocusField_ == 1)
			? modalField2_ : modalField1_;

		if (ev.type == SDL_TEXTINPUT)
		{
			activeField += ev.text.text;
			return;
		}
		if (ev.type == SDL_KEYDOWN)
		{
			SDL_Keycode sym = ev.key.keysym.sym;
			Uint16 mod = ev.key.keysym.mod;
			if (sym == SDLK_ESCAPE)
			{
				CloseModal();
				return;
			}
			if (sym == SDLK_RETURN || sym == SDLK_KP_ENTER)
			{
				ConfirmModal();
				return;
			}
			if (sym == SDLK_TAB && modalMode_ == kModalCustomUrl)
			{
				modalFocusField_ = 1 - modalFocusField_;
				return;
			}
			if (sym == SDLK_BACKSPACE)
			{
				PopLastUtf8Char(activeField);
				return;
			}
			if ((mod & KMOD_CTRL) && sym == SDLK_u)
			{
				activeField.clear();
				return;
			}
			if ((mod & KMOD_CTRL) && sym == SDLK_v)
			{
				char *clip = SDL_GetClipboardText();
				if (clip)
				{
					std::string clean;
					for (const char *p = clip; *p; ++p)
					{
						if (*p != '\r' && *p != '\n') clean.push_back(*p);
					}
					activeField += TrimStr(clean);
					SDL_free(clip);
				}
				return;
			}
		}
		if (ev.type == SDL_MOUSEBUTTONDOWN && ev.button.button == SDL_BUTTON_LEFT)
		{
			int dx = 0, dy = 0;
			if (!WindowToDesign(ev.button.x, ev.button.y, dx, dy))
				return;
			if (modalMode_ == kModalCustomUrl)
			{
				if (InRect(dx, dy, SDL_Rect{ 420, 434, 1080, 58 })) modalFocusField_ = 0;
				else if (InRect(dx, dy, SDL_Rect{ 420, 554, 1080, 58 })) modalFocusField_ = 1;
			}
			if (InRect(dx, dy, SDL_Rect{ 1020, 700, 210, 64 }))
				CloseModal();
			else if (InRect(dx, dy, SDL_Rect{ 1260, 700, 240, 64 }))
				ConfirmModal();
		}
	}

	std::string EffectiveProxyPrefix() const
	{
		std::string p = customProxy_;
		if (p.empty())
		{
			if (selectedProxy_ == 2) p = "https://gh-proxy.cn/";
			else if (selectedProxy_ == 3) p = "https://proxy.craft-hello.top/proxy/";
		}
		if (!p.empty() && p.back() != '/') p.push_back('/');
		return p;
	}

	static std::string ApplyProxy(const std::string &url, const std::string &proxy)
	{
		if (proxy.empty()) return url;
		if (url.compare(0, proxy.size(), proxy) == 0) return url;
		return proxy + url;
	}

	std::string ResolveNewestDataTagBaseUrl(HttpEngine &http, const std::string &proxy)
	{
		if (defaultRepo_.empty()) return "";
		std::string apiUrl = "https://api.github.com/repos/" + defaultRepo_ + "/releases?per_page=100";
		std::string body, err;
		/* Try direct API first (GitHub REST API works directly in most networks,
		 * and fall back to proxied URL if direct fails). */
		if (!http.FetchBytes(apiUrl, 4 * 1024 * 1024, cancelFlag_, body, err))
		{
			if (proxy.empty() || !http.FetchBytes(ApplyProxy(apiUrl, proxy), 4 * 1024 * 1024, cancelFlag_, body, err))
				return "";
		}
		JsonVal root;
		if (!ParseJson(body, root) || root.type != JsonVal::kArray)
			return "";

		int bestN = -1;
		std::string bestTag;
		for (size_t i = 0; i < root.arrVal.size(); ++i)
		{
			const JsonVal &rel = root.arrVal[i];
			if (rel.type != JsonVal::kObject || rel.GetBool("draft", false))
				continue;
			std::string tag = rel.GetStr("tag_name");
			if (tag.compare(0, 6, "data-v") == 0 && tag.size() > 6)
			{
				bool allDigits = true;
				for (size_t k = 6; k < tag.size(); ++k)
				{
					if (tag[k] < '0' || tag[k] > '9') { allDigits = false; break; }
				}
				if (allDigits)
				{
					int n = atoi(tag.c_str() + 6);
					if (n > bestN) { bestN = n; bestTag = tag; }
				}
			}
		}
		if (bestTag.empty()) return "";
		return "https://github.com/" + defaultRepo_ + "/releases/download/" + bestTag + "/";
	}

	void StartDownload()
	{
		if (busy_.exchange(true)) return;
		JoinWorker();

		activeAction_.store(1);
		SetDownloadProgress(0.0, "正在获取资源清单…");
		SetExtractProgress(false, 0.0, "");
		{
			std::lock_guard<std::mutex> lk(uiMutex_);
			errorText_.clear();
		}

		std::string proxy = EffectiveProxyPrefix();
		std::string userUrl = customBaseUrl_;
		std::string defUrl = defaultBaseUrl_;

		worker_ = std::thread([this, proxy, userUrl, defUrl]() {
			RunDownloadPipeline(userUrl, defUrl, proxy);
		});
	}

	void RunDownloadPipeline(const std::string &userUrl, const std::string &defUrl, const std::string &proxy)
	{
		HttpEngine http;
		auto fail = [&](const std::string &msg) {
			SetExtractProgress(false, 0.0, "");
			SetUiStatus("下载未完成，可切换加速节点或改用「导入本地文件」", msg);
			activeAction_.store(0);
			busy_.store(false);
		};

		std::string rawBase = !userUrl.empty() ? userUrl : defUrl;
		std::string manifestUrl;
		std::string assetBase;
		if (EndsWithNoCase(rawBase, ".json"))
		{
			manifestUrl = rawBase;
			size_t sl = rawBase.rfind('/');
			assetBase = (sl != std::string::npos) ? rawBase.substr(0, sl + 1) : rawBase;
		}
		else
		{
			assetBase = rawBase;
			if (!assetBase.empty() && assetBase.back() != '/') assetBase.push_back('/');
			manifestUrl = assetBase + "data-assets.json";
		}

		std::string manifestBody, fetchErr;
		bool gotManifest = http.FetchBytes(ApplyProxy(manifestUrl, proxy), 8 * 1024 * 1024,
		                                   cancelFlag_, manifestBody, fetchErr);

		/* If built-in URL returned 404/error (e.g. newer data-vN tag published),
		 * dynamically discover the highest data-vN tag via GitHub Releases API! */
		if (!gotManifest && userUrl.empty() && !cancelFlag_.load())
		{
			std::string resolvedBase = ResolveNewestDataTagBaseUrl(http, proxy);
			if (!resolvedBase.empty() && resolvedBase != assetBase)
			{
				assetBase = resolvedBase;
				manifestUrl = assetBase + "data-assets.json";
				gotManifest = http.FetchBytes(ApplyProxy(manifestUrl, proxy), 8 * 1024 * 1024,
				                              cancelFlag_, manifestBody, fetchErr);
			}
		}

		if (cancelFlag_.load()) return;
		if (!gotManifest)
		{
			fail("获取资源清单失败: " + fetchErr + " (" + manifestUrl + ")");
			return;
		}

		JsonVal root;
		if (!ParseJson(manifestBody, root) || root.type != JsonVal::kObject)
		{
			fail("资源清单不是合法的 JSON（代理节点可能返回了错误页面，请切换节点重试）");
			return;
		}
		const JsonVal *assetsVal = root.Get("assets");
		if (!assetsVal || assetsVal->type != JsonVal::kArray || assetsVal->arrVal.empty())
		{
			fail("data-assets.json 中没有可下载的分包条目");
			return;
		}

		/* Keep assetBase pointing at the release directory where data-assets.json
		 * was fetched (matching IOSBootstrap.mm & fetch_data_parts.py), because
		 * mirrored data-vN releases may carry an upstream baseUrl inside JSON. */
		std::vector<DataAssetItem> assets;
		int fileTotal = (int)root.GetInt64("fileTotal", 0);
		int sumFileCount = 0;
		for (size_t i = 0; i < assetsVal->arrVal.size(); ++i)
		{
			const JsonVal & item = assetsVal->arrVal[i];
			DataAssetItem a;
			a.name = item.GetStr("name");
			a.size = item.GetInt64("size", 0);
			a.sha256 = ToLowerAscii(TrimStr(item.GetStr("sha256")));
			a.fileCount = (int)item.GetInt64("fileCount", 0);
			if (a.name.empty() || a.name.find('/') != std::string::npos || a.name.find("..") != std::string::npos)
			{
				fail("资源清单包含非法文件名: " + a.name);
				return;
			}
			sumFileCount += a.fileCount;
			assets.push_back(a);
		}
		if (fileTotal <= 0) fileTotal = sumFileCount;

		std::string tmpDir = appRoot_ + "/.tmp";
		EnsureDirRecursive(tmpDir);
		EnsureDirRecursive(appRoot_ + "/data");
		unlink((appRoot_ + "/.complete").c_str());

		/* Serial background extraction queue running alongside downloads */
		struct QueuedPart {
			std::string zipPath;
			int fileCount;
			bool poison;
		};
		std::mutex qMutex;
		std::condition_variable qCv;
		std::deque<QueuedPart> queue;
		std::atomic<bool> extractFailed(false);
		std::string extractErrMsg;
		int extractedBase = 0;

		std::thread extractThread([&]() {
			for (;;)
			{
				QueuedPart item;
				{
					std::unique_lock<std::mutex> lk(qMutex);
					qCv.wait(lk, [&]() { return !queue.empty() || cancelFlag_.load() || extractFailed.load(); });
					if (cancelFlag_.load() || extractFailed.load()) return;
					item = queue.front();
					queue.pop_front();
				}
				if (item.poison)
				{
					SetExtractProgress(false, 1.0, "");
					return;
				}

				std::string stageDir = tmpDir + "/extract-stage";
				RemoveTreeRecursive(stageDir);
				EnsureDirRecursive(stageDir);

				struct ExtractCtx {
					BootstrapWindow *self;
					std::atomic<bool> *cancel;
					int base;
					int total;
					uint32_t lastTick;
				} ectx{ this, &cancelFlag_, extractedBase, fileTotal, 0 };

				char zerr[512] = { 0 };
				int zrc = Krkr_ExtractZip(
					item.zipPath.c_str(),
					stageDir.c_str(),
					[](void *raw, int done, int partTotal, const char *) -> int {
						ExtractCtx *c = (ExtractCtx *)raw;
						if (c->cancel->load()) return 0;
						uint32_t t = SDL_GetTicks();
						if (done == partTotal || t - c->lastTick >= 60)
						{
							c->lastTick = t;
							int overallTotal = c->total > 0 ? c->total : (c->base + partTotal);
							int overallDone = c->base + done;
							double r = overallTotal > 0 ? (double)overallDone / (double)overallTotal : 0.0;
							c->self->SetExtractProgress(
								true, r,
								"正在解压：" + std::to_string(overallDone) + " / " +
								std::to_string(overallTotal) + " 个文件");
						}
						return 1;
					},
					&ectx, zerr, sizeof(zerr));

				if (zrc != 0)
				{
					RemoveTreeRecursive(stageDir);
					if (!cancelFlag_.load())
					{
						extractErrMsg = std::string("解压失败: ") + (zerr[0] ? zerr : "压缩包损坏");
						extractFailed.store(true);
					}
					return;
				}

				std::string mergeErr;
				if (!MergeIntoDataDir(stageDir, appRoot_, nullptr, nullptr, &mergeErr))
				{
					RemoveTreeRecursive(stageDir);
					extractErrMsg = "合并游戏数据失败: " + mergeErr;
					extractFailed.store(true);
					return;
				}
				RemoveTreeRecursive(stageDir);
				unlink(item.zipPath.c_str());
				extractedBase += item.fileCount;
			}
		});

		auto stopExtractor = [&]() {
			{
				std::lock_guard<std::mutex> lk(qMutex);
				queue.push_back(QueuedPart{ "", 0, true });
			}
			qCv.notify_all();
			if (extractThread.joinable()) extractThread.join();
		};

		/* Download + SHA-256 verify each asset */
		for (size_t i = 0; i < assets.size(); ++i)
		{
			if (cancelFlag_.load() || extractFailed.load()) break;
			const DataAssetItem &asset = assets[i];
			std::string partPath = tmpDir + "/" + asset.name;

			bool reused = false;
			if (asset.size > 0 && FileSizeOf(partPath) == asset.size)
			{
				SetDownloadProgress(
					((double)i + 0.5) / (double)assets.size(),
					"正在校验已有缓存 " + asset.name + " …");
				if (asset.sha256.empty() || Sha256FileHex(partPath, cancelFlag_) == asset.sha256)
					reused = true;
				else
					unlink(partPath.c_str());
			}

			if (!reused)
			{
				std::string dlUrl = ApplyProxy(assetBase + asset.name, proxy);
				auto tStart = std::chrono::steady_clock::now();
				std::atomic<uint32_t> lastUiTick(0);

				std::string dlErr;
				bool ok = http.DownloadFile(
					dlUrl, partPath, asset.size, cancelFlag_,
					[&](int64_t done, int64_t total) {
						uint32_t nowTick = SDL_GetTicks();
						uint32_t prev = lastUiTick.load();
						if (done < total && nowTick - prev < 60) return;
						lastUiTick.store(nowTick);

						double partRatio = total > 0 ? std::min(1.0, (double)done / (double)total) : 0.0;
						double overall = ((double)i + partRatio) / (double)assets.size();
						double elapsed = std::chrono::duration<double>(
							std::chrono::steady_clock::now() - tStart).count();
						double speed = elapsed > 0.15 ? ((double)done / elapsed) : 0.0;
						int pct = (int)std::round(partRatio * 100.0);

						std::string line = "正在下载 (" + std::to_string(i + 1) + "/" +
						                   std::to_string(assets.size()) + ") " + asset.name + "  " +
						                   std::to_string(pct) + "%  " + FormatBytes((double)done);
						if (total > 0) line += " / " + FormatBytes((double)total);
						if (speed > 0.0) line += "  (" + FormatBytes(speed) + "/s)";
						SetDownloadProgress(overall, line);
					},
					dlErr);

				if (cancelFlag_.load()) { stopExtractor(); return; }
				if (!ok)
				{
					unlink(partPath.c_str());
					stopExtractor();
					fail("下载 " + asset.name + " 失败: " + dlErr);
					return;
				}

				if (asset.size > 0 && FileSizeOf(partPath) != asset.size)
				{
					unlink(partPath.c_str());
					stopExtractor();
					fail(asset.name + " 文件大小不匹配");
					return;
				}
				if (!asset.sha256.empty())
				{
					SetDownloadProgress(
						((double)i + 0.98) / (double)assets.size(),
						"正在校验 SHA-256: " + asset.name + " …");
					std::string gotHash = Sha256FileHex(partPath, cancelFlag_);
					if (cancelFlag_.load()) { stopExtractor(); return; }
					if (gotHash != asset.sha256)
					{
						unlink(partPath.c_str());
						stopExtractor();
						fail(asset.name + " SHA-256 校验失败，请重试");
						return;
					}
				}
			}

			{
				std::lock_guard<std::mutex> lk(qMutex);
				queue.push_back(QueuedPart{ partPath, asset.fileCount, false });
			}
			qCv.notify_one();
		}

		SetDownloadProgress(1.0, "全部分包下载完成，正在等待后台解压收尾…");
		stopExtractor();

		if (cancelFlag_.load()) return;
		if (extractFailed.load())
		{
			fail(extractErrMsg.empty() ? "解压过程出错" : extractErrMsg);
			return;
		}

		if (!IsRegularFile(appRoot_ + "/data/startup.tjs"))
		{
			fail("解压完成但未找到 startup.tjs，请检查数据源配置");
			return;
		}

		RemoveTreeRecursive(tmpDir);
		ClearPackRecords(appRoot_);
		WriteWholeFile(appRoot_ + "/.complete", "ok\n");
		SetDownloadProgress(1.0, "游戏资源准备就绪，正在启动…");
		readyToStart_.store(true);
	}

	void StartPickerAndImport()
	{
		if (busy_.exchange(true)) return;
		JoinWorker();

		activeAction_.store(2);
		SetDownloadProgress(0.0, "正在打开文件选择器（支持一次多选全部 .zip 分包或选择 data.xp3）…");
		{
			std::lock_guard<std::mutex> lk(uiMutex_);
			errorText_.clear();
		}

		worker_ = std::thread([this]() {
			std::vector<std::string> picked;
			bool pickerAvail = false;
			bool ok = OpenSystemFilePicker(picked, pickerAvail);
			if (cancelFlag_.load()) return;

			if (!pickerAvail)
			{
				activeAction_.store(0);
				busy_.store(false);
				SetUiStatus("可直接将文件拖入窗口，或在弹窗中输入路径", "");
				/* Post synthetic event to open path modal on main UI thread */
				SDL_Event userEv;
				SDL_zero(userEv);
				userEv.type = SDL_USEREVENT;
				userEv.user.code = 1001;
				SDL_PushEvent(&userEv);
				return;
			}
			if (!ok || picked.empty())
			{
				SetUiStatus("已取消选择文件", "");
				activeAction_.store(0);
				busy_.store(false);
				return;
			}
			std::vector<std::string> expanded;
			ExpandInputPathList(picked, expanded);
			RunImportList(expanded);
		});
	}

	void StartImportFiles(const std::vector<std::string> &files)
	{
		if (busy_.exchange(true)) return;
		JoinWorker();
		activeAction_.store(2);
		{
			std::lock_guard<std::mutex> lk(uiMutex_);
			errorText_.clear();
		}
		worker_ = std::thread([this, files]() {
			RunImportList(files);
		});
	}

	void RunImportList(std::vector<std::string> files)
	{
		auto fail = [&](const std::string &msg) {
			SetExtractProgress(false, 0.0, "");
			SetUiStatus("导入未完成", msg);
			activeAction_.store(0);
			busy_.store(false);
		};

		if (files.empty())
		{
			fail("未选择有效的 .zip 或 data.xp3 文件");
			return;
		}
		std::sort(files.begin(), files.end());

		std::string tmpDir = appRoot_ + "/.tmp-import";
		EnsureDirRecursive(tmpDir);
		EnsureDirRecursive(appRoot_ + "/data");
		unlink((appRoot_ + "/.complete").c_str());

		int highestPackCount = 0;
		std::vector<int> importedIndices;

		for (size_t i = 0; i < files.size(); ++i)
		{
			if (cancelFlag_.load()) return;
			const std::string &src = files[i];
			std::string baseName = BaseNameOf(src);

			SetDownloadProgress((double)i / (double)files.size(),
			                    "正在导入 (" + std::to_string(i + 1) + "/" +
			                    std::to_string(files.size()) + ") " + baseName + " …");

			std::string stageDir = tmpDir + "/stage";
			RemoveTreeRecursive(stageDir);
			EnsureDirRecursive(stageDir);

			if (EndsWithNoCase(baseName, ".xp3"))
			{
				struct Xp3Ctx {
					BootstrapWindow *self;
					std::atomic<bool> *cancel;
					std::string name;
					uint32_t lastTick;
				} xctx{ this, &cancelFlag_, baseName, 0 };

				OHOSXp3ExtractResult res;
				memset(&res, 0, sizeof(res));
				int xrc = OHOS_ExtractXp3(
					src.c_str(), stageDir.c_str(),
					[](void *raw, int done, int total, const char *) -> int {
						Xp3Ctx *c = (Xp3Ctx *)raw;
						if (c->cancel->load()) return 0;
						uint32_t t = SDL_GetTicks();
						if (done == total || t - c->lastTick >= 60)
						{
							c->lastTick = t;
							double r = total > 0 ? (double)done / (double)total : 0.0;
							c->self->SetExtractProgress(
								true, r,
								"正在解包 " + c->name + "：" + std::to_string(done) +
								" / " + std::to_string(total) + " 个文件");
						}
						return 1;
					},
					&xctx, &res);

				if (xrc != 0)
				{
					RemoveTreeRecursive(stageDir);
					if (cancelFlag_.load()) return;
					fail(std::string("XP3 解包失败: ") + (res.error[0] ? res.error : "文件格式不支持"));
					return;
				}
			}
			else if (EndsWithNoCase(baseName, ".zip"))
			{
				struct ZipCtx {
					BootstrapWindow *self;
					std::atomic<bool> *cancel;
					std::string name;
					uint32_t lastTick;
				} zctx{ this, &cancelFlag_, baseName, 0 };

				char zerr[512] = { 0 };
				int zrc = Krkr_ExtractZip(
					src.c_str(), stageDir.c_str(),
					[](void *raw, int done, int total, const char *) -> int {
						ZipCtx *c = (ZipCtx *)raw;
						if (c->cancel->load()) return 0;
						uint32_t t = SDL_GetTicks();
						if (done == total || t - c->lastTick >= 60)
						{
							c->lastTick = t;
							double r = total > 0 ? (double)done / (double)total : 0.0;
							c->self->SetExtractProgress(
								true, r,
								"正在解压 " + c->name + "：" + std::to_string(done) +
								" / " + std::to_string(total) + " 个文件");
						}
						return 1;
					},
					&zctx, zerr, sizeof(zerr));

				if (zrc != 0)
				{
					RemoveTreeRecursive(stageDir);
					if (cancelFlag_.load()) return;
					fail("解压 " + baseName + " 失败: " + (zerr[0] ? zerr : "压缩包无效"));
					return;
				}
			}
			else
			{
				RemoveTreeRecursive(stageDir);
				fail("不支持的文件格式: " + baseName + "（请选择 .zip 分包或 data.xp3）");
				return;
			}

			int packIdx = 0, packCnt = 0;
			std::string mergeErr;
			if (!MergeIntoDataDir(stageDir, appRoot_, &packIdx, &packCnt, &mergeErr))
			{
				RemoveTreeRecursive(stageDir);
				fail("合并数据失败: " + mergeErr);
				return;
			}
			RemoveTreeRecursive(stageDir);
			if (packIdx > 0) importedIndices.push_back(packIdx);
			if (packCnt > highestPackCount) highestPackCount = packCnt;
		}

		RemoveTreeRecursive(tmpDir);
		SetExtractProgress(false, 1.0, "");

		std::vector<int> missing = MissingPackIndices(appRoot_, highestPackCount);
		if (!missing.empty())
		{
			std::string doneDesc = importedIndices.empty()
				? "部分数据包"
				: FormatPackIndexList(importedIndices);
			SetUiStatus(
				"已导入" + doneDesc + "，还缺：" + FormatPackIndexList(missing) +
				" — 请点击「导入本地文件」继续选择剩余 zip（可一次多选）",
				"");
			activeAction_.store(0);
			busy_.store(false);
			return;
		}

		if (!IsRegularFile(appRoot_ + "/data/startup.tjs"))
		{
			fail("已解压但未找到 startup.tjs（若是多卷分包请确认已导入全部 data-part*.zip）");
			return;
		}

		ClearPackRecords(appRoot_);
		WriteWholeFile(appRoot_ + "/.complete", "ok\n");
		SetDownloadProgress(1.0, "本地资源导入完成，正在启动游戏…");
		readyToStart_.store(true);
	}

	std::string appRoot_;
	std::string assetDir_;
	std::string defaultRepo_;
	std::string defaultBaseUrl_;
	std::string customBaseUrl_;
	std::string customProxy_;

	SDL_Window *window_;
	SDL_Surface *canvas_;
	FontRenderer font_;

	SDL_Surface *artBg_ = nullptr;
	SDL_Surface *artDirect_ = nullptr;
	SDL_Surface *artDirectSel_ = nullptr;
	SDL_Surface *artGh_ = nullptr;
	SDL_Surface *artGhSel_ = nullptr;
	SDL_Surface *artCraft_ = nullptr;
	SDL_Surface *artCraftSel_ = nullptr;
	SDL_Surface *artTrack_ = nullptr;
	SDL_Surface *artDownload_ = nullptr;
	SDL_Surface *artDownloadAct_ = nullptr;
	SDL_Surface *artImport_ = nullptr;
	SDL_Surface *artImportAct_ = nullptr;
	SDL_Surface *artIcon_ = nullptr;

	std::atomic<bool> cancelFlag_;
	std::atomic<bool> readyToStart_;
	std::atomic<bool> busy_;
	int selectedProxy_;
	std::atomic<int> activeAction_;
	int hoverProxy_;
	int hoverAction_;

	std::mutex uiMutex_;
	double progress_;
	double extractProgress_;
	bool extractVisible_;
	std::string progressText_;
	std::string extractText_;
	std::string errorText_;

	ModalMode modalMode_;
	int modalFocusField_;
	std::string modalField1_;
	std::string modalField2_;
	std::vector<std::string> pendingDrops_;

	uint32_t downloadMouseDownTick_;
	bool downloadLongPressTriggered_;

	std::thread worker_;
};

static std::string ResolveBootstrapAssetDir(const std::string &exeDir)
{
	std::vector<std::string> dirs;
	const char *envDir = getenv("KRKR_LINUX_BOOTSTRAP_ASSETS");
	if (envDir && envDir[0])
		dirs.push_back(envDir);
	dirs.push_back(exeDir + "/../share/yosuganosora/bootstrap");
	dirs.push_back(exeDir + "/../share/yosuga-no-sora-remake/bootstrap");
	dirs.push_back(exeDir + "/bootstrap");
	dirs.push_back(exeDir + "/src/resources/ios");
	dirs.push_back("src/resources/ios");

	for (size_t i = 0; i < dirs.size(); ++i)
	{
		if (IsRegularFile(dirs[i] + "/Background.png"))
			return dirs[i];
	}
	for (size_t i = 0; i < dirs.size(); ++i)
	{
		if (IsDirectory(dirs[i]))
			return dirs[i];
	}
	return "";
}

} // namespace

extern "C" int krkrsdl2_linux_run_bootstrap(int argc, char **argv)
{
	g_activeDataRoot.clear();

	const char *skipEnv = getenv("KRKR_SKIP_BOOTSTRAP");
	if (skipEnv && strcmp(skipEnv, "1") == 0)
		return 1;

	/* 1. Explicit CLI positional path argument (Flatpak, Linglong, dev script,
	 *    or user passing /path/to/data) -> engine handles it directly. */
	for (int i = 1; i < argc; ++i)
	{
		if (!argv[i]) continue;
		if (strcmp(argv[i], "--") == 0) break;
		if (argv[i][0] == '-') continue;
		if (PathExists(argv[i]))
			return 1;
	}

	/* 2. Bundled game data alongside executable (standard Tarball / dev build). */
	std::string exeDir = GetExeDir();
	if (HasPlayableDataInRoot(exeDir))
		return 1;

	/* 3. Portable mode: data/ or data.xp3 placed right next to the .AppImage file. */
	const char *appImageEnv = getenv("APPIMAGE");
	if (appImageEnv && appImageEnv[0])
	{
		std::string appImgDir = DirNameOf(appImageEnv);
		if (!appImgDir.empty() && HasPlayableDataInRoot(appImgDir) &&
		    MissingPackIndices(appImgDir, 0).empty())
		{
			g_activeDataRoot = appImgDir;
			return 1;
		}
	}

	/* 4. Per-user XDG external data root (${XDG_DATA_HOME:-~/.local/share}/<app-id>). */
	std::string xdgRoot = ResolveXdgDataRoot();
	if (HasPlayableDataInRoot(xdgRoot) &&
	    (IsRegularFile(xdgRoot + "/.complete") || MissingPackIndices(xdgRoot, 0).empty()))
	{
		g_activeDataRoot = xdgRoot;
		return 1;
	}

	/* 5. Missing or incomplete external data -> launch the built-in Bootstrap UI! */
	EnsureDirRecursive(xdgRoot);
	std::string assetDir = ResolveBootstrapAssetDir(exeDir);
	BootstrapWindow ui(xdgRoot, assetDir);
	if (!ui.Run())
		return 0;

	g_activeDataRoot = xdgRoot;
	return 1;
}

extern "C" const char *krkrsdl2_linux_data_root(void)
{
	return g_activeDataRoot.empty() ? nullptr : g_activeDataRoot.c_str();
}

#else

extern "C" int krkrsdl2_linux_run_bootstrap(int, char **)
{
	return 1;
}

extern "C" const char *krkrsdl2_linux_data_root(void)
{
	return nullptr;
}

#endif /* __linux__ && !__ANDROID__ && !__OHOS__ */
