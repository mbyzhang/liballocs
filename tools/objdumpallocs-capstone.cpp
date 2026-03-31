#include <algorithm>
#include <cinttypes>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <elf.h>
#include <fcntl.h>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>
#include <string_view>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include <capstone/capstone.h>

namespace
{

struct Symbol
{
    uint64_t addr;
    uint64_t size;
    bool is_func;
    bool is_defined;
    std::string name;
};

struct SiteKey
{
    uint32_t sec_index;
    uint64_t offset;
    bool operator==(const SiteKey& other) const
    {
        return sec_index == other.sec_index && offset == other.offset;
    }
};

struct SiteKeyHash
{
    std::size_t operator()(const SiteKey& k) const
    {
        return (static_cast<std::size_t>(k.sec_index) << 32) ^ static_cast<std::size_t>(k.offset);
    }
};

struct CallSite
{
    uint64_t call_addr;
    uint64_t return_addr;
};

struct OutputRec
{
    std::string return_sym;
    uint64_t return_addr;
    std::string return_off;
    std::string filename;
    int line;
    int line_end;
    std::string token;
    std::string source;
};

struct LineInfo
{
    std::string func;
    std::string file;
    int line;
};

struct SecRange
{
    uint64_t start;
    uint64_t end;
    std::string name;
};

struct MappedFile
{
    int fd = -1;
    std::size_t size = 0;
    const unsigned char* data = nullptr;

    ~MappedFile()
    {
        if (data && size) munmap(const_cast<unsigned char*>(data), size);
        if (fd >= 0) close(fd);
    }
};

bool starts_with(const std::string& s, const std::string& p)
{
    return s.size() >= p.size() && s.compare(0, p.size(), p) == 0;
}

bool ends_with(const std::string& s, const std::string& suffix)
{
    return s.size() >= suffix.size() && s.compare(s.size() - suffix.size(), suffix.size(), suffix) == 0;
}

std::string trim(std::string s)
{
    while (!s.empty() && std::isspace(static_cast<unsigned char>(s.back()))) s.pop_back();
    std::size_t i = 0;
    while (i < s.size() && std::isspace(static_cast<unsigned char>(s[i]))) ++i;
    return s.substr(i);
}

std::string collapse_ws(const std::string& s)
{
    std::string out;
    out.reserve(s.size());
    bool in_ws = false;
    for (unsigned char ch : s)
    {
        if (std::isspace(ch))
        {
            if (!out.empty()) in_ws = true;
            continue;
        }
        if (in_ws)
        {
            out.push_back(' ');
            in_ws = false;
        }
        out.push_back(static_cast<char>(ch));
    }
    return trim(out);
}

std::string extract_alloc_token(const std::string& source)
{
    auto extract_after = [&](std::size_t pos, std::size_t kw_len) {
        std::size_t i = pos + kw_len;
        while (i < source.size() && !std::isalnum(static_cast<unsigned char>(source[i]))
            && source[i] != '_' && source[i] != '*') ++i;

        std::size_t end = i;
        while (end < source.size())
        {
            unsigned char ch = static_cast<unsigned char>(source[end]);
            if (std::isalnum(ch) || ch == '_' || ch == '*' || std::isspace(ch)) ++end;
            else break;
        }
        return collapse_ws(source.substr(i, end - i));
    };

    std::size_t pos = source.rfind("sizeof");
    if (pos != std::string::npos)
    {
        std::string token = extract_after(pos, 6);
        if (!token.empty()) return token;
    }

    pos = source.rfind("new");
    if (pos != std::string::npos)
    {
        std::string token = extract_after(pos, 3);
        if (!token.empty()) return token;
    }

    return "$FAILED$";
}

struct SourceCache
{
    std::unordered_map<std::string, std::vector<std::string>> lines_by_file;

    std::string get_line(const std::string& path, int line_number)
    {
        if (path.empty() || path == "??" || line_number <= 0) return "";

        auto it = lines_by_file.find(path);
        if (it == lines_by_file.end())
        {
            std::ifstream in(path);
            std::vector<std::string> lines;
            std::string line;
            while (std::getline(in, line)) lines.push_back(line);
            it = lines_by_file.emplace(path, std::move(lines)).first;
        }

        if (static_cast<std::size_t>(line_number) > it->second.size()) return "";
        return it->second[line_number - 1];
    }
};

std::string shell_quote(const std::string& s)
{
    std::string out = "'";
    for (char c : s)
    {
        if (c == '\'') out += "'\\''";
        else out += c;
    }
    out += "'";
    return out;
}

std::string strip_at_version(const std::string& s)
{
    std::size_t p = s.find('@');
    if (p == std::string::npos) return s;
    return s.substr(0, p);
}

bool is_obstack_name(const std::string& s)
{
    return s.find("obstack") != std::string::npos;
}

std::vector<std::string> split_ws(const std::string& s)
{
    std::vector<std::string> out;
    std::istringstream iss(s);
    std::string tok;
    while (iss >> tok) out.push_back(tok);
    return out;
}

std::unordered_set<std::string> build_alloc_names()
{
    std::unordered_set<std::string> names = {
        "malloc", "calloc", "realloc", "memalign", "posix_memalign", "valloc", "alloca", "__monalloca_"
    };
    std::vector<std::string> stock_names = {
        "malloc", "calloc", "realloc", "memalign", "posix_memalign", "valloc", "alloca"
    };
    for (const auto& name : stock_names) names.insert("__wrap_" + name);

    auto add_desc_names = [&](const char* env_value) {
        if (!env_value || !*env_value) return;
        auto toks = split_ws(env_value);
        for (const auto& t : toks)
        {
            std::size_t l = t.find('(');
            std::size_t r = t.find(')');
            if (l == std::string::npos || r == std::string::npos || r <= l) continue;
            std::string n = t.substr(0, l);
            if (n.empty()) continue;
            names.insert(n);
            names.insert("__wrap_" + n);
        }
    };

    add_desc_names(std::getenv("LIBALLOCS_ALLOC_FNS"));
    add_desc_names(std::getenv("LIBALLOCS_SUBALLOC_FNS"));
    add_desc_names(std::getenv("LIBALLOCS_ALLOCSZ_FNS"));
    return names;
}

bool map_file(const std::string& path, MappedFile& mf)
{
    mf.fd = open(path.c_str(), O_RDONLY);
    if (mf.fd < 0) return false;

    struct stat st;
    if (fstat(mf.fd, &st) != 0) return false;
    if (st.st_size <= 0) return false;

    mf.size = static_cast<std::size_t>(st.st_size);
    void* p = mmap(nullptr, mf.size, PROT_READ, MAP_PRIVATE, mf.fd, 0);
    if (p == MAP_FAILED) return false;
    mf.data = reinterpret_cast<const unsigned char*>(p);
    return true;
}

const char* sec_name(const Elf64_Ehdr* eh, const Elf64_Shdr* shdrs, std::size_t idx, const unsigned char* base)
{
    const Elf64_Shdr& shstr = shdrs[eh->e_shstrndx];
    const char* strs = reinterpret_cast<const char*>(base + shstr.sh_offset);
    return strs + shdrs[idx].sh_name;
}

void load_symbols(const Elf64_Ehdr* eh, const Elf64_Shdr* shdrs, const unsigned char* base, std::vector<Symbol>& out)
{
    for (std::size_t i = 0; i < eh->e_shnum; ++i)
    {
        const Elf64_Shdr& sh = shdrs[i];
        if (sh.sh_type != SHT_SYMTAB && sh.sh_type != SHT_DYNSYM) continue;
        if (sh.sh_entsize != sizeof(Elf64_Sym)) continue;
        if (sh.sh_link >= eh->e_shnum) continue;

        const Elf64_Shdr& str_sh = shdrs[sh.sh_link];
        const char* strtab = reinterpret_cast<const char*>(base + str_sh.sh_offset);
        std::size_t count = sh.sh_size / sh.sh_entsize;
        const Elf64_Sym* syms = reinterpret_cast<const Elf64_Sym*>(base + sh.sh_offset);

        for (std::size_t s = 0; s < count; ++s)
        {
            const Elf64_Sym& sym = syms[s];
            if (sym.st_name == 0) continue;
            std::string name = strtab + sym.st_name;
            if (name.empty()) continue;
            unsigned stt = ELF64_ST_TYPE(sym.st_info);
            bool is_func = (stt == STT_FUNC || stt == STT_NOTYPE);
            bool is_defined = (sym.st_shndx != SHN_UNDEF);
            out.push_back(Symbol{sym.st_value, sym.st_size, is_func, is_defined, std::move(name)});
        }
    }
}

void load_relocations(
    const Elf64_Ehdr* eh,
    const Elf64_Shdr* shdrs,
    const unsigned char* base,
    std::unordered_map<uint64_t, std::string>& by_va,
    std::unordered_map<SiteKey, std::string, SiteKeyHash>& by_site)
{
    for (std::size_t i = 0; i < eh->e_shnum; ++i)
    {
        const Elf64_Shdr& relsh = shdrs[i];
        if (relsh.sh_type != SHT_RELA && relsh.sh_type != SHT_REL) continue;
        if (relsh.sh_link >= eh->e_shnum || relsh.sh_info >= eh->e_shnum) continue;

        const Elf64_Shdr& symsh = shdrs[relsh.sh_link];
        if ((symsh.sh_type != SHT_SYMTAB && symsh.sh_type != SHT_DYNSYM) || symsh.sh_entsize != sizeof(Elf64_Sym)) continue;
        const Elf64_Shdr& strsh = shdrs[symsh.sh_link];
        const char* strtab = reinterpret_cast<const char*>(base + strsh.sh_offset);
        const Elf64_Sym* syms = reinterpret_cast<const Elf64_Sym*>(base + symsh.sh_offset);
        std::size_t nsyms = symsh.sh_size / symsh.sh_entsize;

        const Elf64_Shdr& tgt = shdrs[relsh.sh_info];

        if (relsh.sh_type == SHT_RELA)
        {
            const Elf64_Rela* rels = reinterpret_cast<const Elf64_Rela*>(base + relsh.sh_offset);
            std::size_t n = relsh.sh_size / sizeof(Elf64_Rela);
            for (std::size_t r = 0; r < n; ++r)
            {
                uint32_t symi = ELF64_R_SYM(rels[r].r_info);
                if (symi >= nsyms) continue;
                const Elf64_Sym& sym = syms[symi];
                if (sym.st_name == 0) continue;
                std::string name = strtab + sym.st_name;
                if (name.empty()) continue;

                uint64_t r_off = rels[r].r_offset;
                by_va[r_off] = name;
                by_site[SiteKey{static_cast<uint32_t>(relsh.sh_info), r_off}] = name;
                if (tgt.sh_addr != 0) by_va[tgt.sh_addr + r_off] = name;
            }
        }
        else
        {
            const Elf64_Rel* rels = reinterpret_cast<const Elf64_Rel*>(base + relsh.sh_offset);
            std::size_t n = relsh.sh_size / sizeof(Elf64_Rel);
            for (std::size_t r = 0; r < n; ++r)
            {
                uint32_t symi = ELF64_R_SYM(rels[r].r_info);
                if (symi >= nsyms) continue;
                const Elf64_Sym& sym = syms[symi];
                if (sym.st_name == 0) continue;
                std::string name = strtab + sym.st_name;
                if (name.empty()) continue;

                uint64_t r_off = rels[r].r_offset;
                by_va[r_off] = name;
                by_site[SiteKey{static_cast<uint32_t>(relsh.sh_info), r_off}] = name;
                if (tgt.sh_addr != 0) by_va[tgt.sh_addr + r_off] = name;
            }
        }
    }
}

std::unordered_map<uint64_t, std::string> load_plt_symbol_map(
    const Elf64_Ehdr* eh,
    const Elf64_Shdr* shdrs,
    const unsigned char* base,
    const std::unordered_map<uint64_t, std::string>& reloc_by_va)
{
    std::unordered_map<uint64_t, std::string> out;

    int plt_idx = -1;
    int plt_got_idx = -1;
    int plt_sec_idx = -1;
    for (std::size_t i = 0; i < eh->e_shnum; ++i)
    {
        std::string n = sec_name(eh, shdrs, i, base);
        if (n == ".plt") plt_idx = static_cast<int>(i);
        if (n == ".plt.got") plt_got_idx = static_cast<int>(i);
        if (n == ".plt.sec") plt_sec_idx = static_cast<int>(i);
    }

    std::vector<std::string> plt_names;
    for (std::size_t i = 0; i < eh->e_shnum; ++i)
    {
        const Elf64_Shdr& relsh = shdrs[i];
        if (relsh.sh_type != SHT_RELA && relsh.sh_type != SHT_REL) continue;

        std::string rel_name = sec_name(eh, shdrs, i, base);
        if (rel_name != ".rela.plt" && rel_name != ".rela.plt.sec" && rel_name != ".rel.plt" && rel_name != ".rel.plt.sec") continue;
        if (relsh.sh_link >= eh->e_shnum) continue;

        const Elf64_Shdr& symsh = shdrs[relsh.sh_link];
        if ((symsh.sh_type != SHT_SYMTAB && symsh.sh_type != SHT_DYNSYM) || symsh.sh_entsize != sizeof(Elf64_Sym)) continue;
        if (symsh.sh_link >= eh->e_shnum) continue;

        const Elf64_Shdr& strsh = shdrs[symsh.sh_link];
        const char* strtab = reinterpret_cast<const char*>(base + strsh.sh_offset);
        const Elf64_Sym* syms = reinterpret_cast<const Elf64_Sym*>(base + symsh.sh_offset);
        std::size_t nsyms = symsh.sh_size / symsh.sh_entsize;

        if (relsh.sh_type == SHT_RELA)
        {
            const Elf64_Rela* rels = reinterpret_cast<const Elf64_Rela*>(base + relsh.sh_offset);
            std::size_t n = relsh.sh_size / sizeof(Elf64_Rela);
            for (std::size_t r = 0; r < n; ++r)
            {
                uint32_t symi = ELF64_R_SYM(rels[r].r_info);
                if (symi >= nsyms || syms[symi].st_name == 0)
                {
                    plt_names.emplace_back();
                    continue;
                }
                plt_names.emplace_back(strtab + syms[symi].st_name);
            }
        }
        else
        {
            const Elf64_Rel* rels = reinterpret_cast<const Elf64_Rel*>(base + relsh.sh_offset);
            std::size_t n = relsh.sh_size / sizeof(Elf64_Rel);
            for (std::size_t r = 0; r < n; ++r)
            {
                uint32_t symi = ELF64_R_SYM(rels[r].r_info);
                if (symi >= nsyms || syms[symi].st_name == 0)
                {
                    plt_names.emplace_back();
                    continue;
                }
                plt_names.emplace_back(strtab + syms[symi].st_name);
            }
        }
    }

    if (!plt_names.empty() && plt_sec_idx >= 0)
    {
        const Elf64_Shdr& plt = shdrs[plt_sec_idx];
        uint64_t entsz = (plt.sh_entsize != 0) ? plt.sh_entsize : 16;
        for (std::size_t i = 0; i < plt_names.size(); ++i)
        {
            if (plt_names[i].empty()) continue;
            out[plt.sh_addr + i * entsz] = plt_names[i];
        }
    }

    if (!plt_names.empty() && plt_idx >= 0)
    {
        const Elf64_Shdr& plt = shdrs[plt_idx];
        uint64_t entsz = (plt.sh_entsize != 0) ? plt.sh_entsize : 16;
        for (std::size_t i = 0; i < plt_names.size(); ++i)
        {
            if (plt_names[i].empty()) continue;
            out[plt.sh_addr + (i + 1) * entsz] = plt_names[i];
        }
    }

    if (plt_got_idx >= 0)
    {
        const Elf64_Shdr& plt_got = shdrs[plt_got_idx];
        const unsigned char* sec = base + plt_got.sh_offset;
        uint64_t entsz = (plt_got.sh_entsize != 0) ? plt_got.sh_entsize : 16;
        std::size_t nent = plt_got.sh_size / entsz;
        for (std::size_t i = 0; i < nent; ++i)
        {
            const unsigned char* stub = sec + i * entsz;
            std::size_t jmp_off = 0;
            if (entsz >= 10 && std::memcmp(stub, "\xf3\x0f\x1e\xfa", 4) == 0) jmp_off = 4;
            if (jmp_off + 6 > entsz) continue;
            if (stub[jmp_off] != 0xff || stub[jmp_off + 1] != 0x25) continue;

            int32_t disp = 0;
            std::memcpy(&disp, stub + jmp_off + 2, sizeof(disp));
            uint64_t stub_addr = plt_got.sh_addr + i * entsz;
            uint64_t got_addr = stub_addr + jmp_off + 6 + static_cast<int64_t>(disp);

            auto it = reloc_by_va.find(got_addr);
            if (it != reloc_by_va.end()) out[stub_addr] = it->second;
        }
    }

    for (std::size_t i = 0; i < eh->e_shnum; ++i)
    {
        const Elf64_Shdr& sh = shdrs[i];
        if (sh.sh_type != SHT_SYMTAB && sh.sh_type != SHT_DYNSYM) continue;
        if (sh.sh_entsize != sizeof(Elf64_Sym)) continue;
        if (sh.sh_link >= eh->e_shnum) continue;

        const Elf64_Shdr& str_sh = shdrs[sh.sh_link];
        const char* strtab = reinterpret_cast<const char*>(base + str_sh.sh_offset);
        std::size_t count = sh.sh_size / sh.sh_entsize;
        const Elf64_Sym* syms = reinterpret_cast<const Elf64_Sym*>(base + sh.sh_offset);

        for (std::size_t s = 0; s < count; ++s)
        {
            const Elf64_Sym& sym = syms[s];
            if (sym.st_name == 0 || sym.st_shndx == SHN_UNDEF) continue;
            if (ELF64_ST_TYPE(sym.st_info) != STT_FUNC) continue;

            std::string name = strtab + sym.st_name;
            if (!ends_with(name, "@plt")) continue;
            out.emplace(sym.st_value, std::move(name));
        }
    }

    return out;
}

const Symbol* find_function_for_addr(
    const std::vector<const Symbol*>& funcs,
    const std::vector<const Symbol*>& zero_size_funcs,
    uint64_t addr)
{
    auto it = std::upper_bound(
        funcs.begin(),
        funcs.end(),
        addr,
        [](uint64_t value, const Symbol* sym) { return value < sym->addr; });

    if (it != funcs.begin())
    {
        const Symbol* candidate = *std::prev(it);
        if (addr < candidate->addr + candidate->size) return candidate;
    }

    auto zero_it = std::upper_bound(
        zero_size_funcs.begin(),
        zero_size_funcs.end(),
        addr,
        [](uint64_t value, const Symbol* sym) { return value < sym->addr; });

    return (zero_it != zero_size_funcs.begin()) ? *std::prev(zero_it) : nullptr;
}

const Symbol* find_symbol_exact(const std::unordered_map<uint64_t, const Symbol*>& syms_by_addr, uint64_t addr)
{
    auto it = syms_by_addr.find(addr);
    return (it != syms_by_addr.end()) ? it->second : nullptr;
}

std::string section_name_for_addr(const std::vector<SecRange>& secs, uint64_t addr)
{
    for (const auto& s : secs)
    {
        if (addr >= s.start && addr < s.end) return s.name;
    }
    return "";
}

bool addr_in_section_prefix(const std::vector<SecRange>& secs, uint64_t addr, const std::string& prefix)
{
    for (const auto& s : secs)
    {
        if (addr < s.start || addr >= s.end) continue;
        if (s.name.rfind(prefix, 0) == 0) return true;
    }
    return false;
}

std::string plt_name_for_addr(const std::unordered_map<uint64_t, std::string>& plt_by_addr, uint64_t addr)
{
    uint64_t best = 0;
    const std::string* name = nullptr;
    for (const auto& kv : plt_by_addr)
    {
        uint64_t stub = kv.first;
        if (addr < stub || addr >= stub + 16) continue;
        if (!name || stub > best)
        {
            best = stub;
            name = &kv.second;
        }
    }
    return name ? *name : "";
}

std::string plt_name_for_addr(
    const std::unordered_map<uint64_t, std::string>& plt_by_addr,
    const std::unordered_map<uint64_t, const Symbol*>& syms_by_addr,
    uint64_t addr)
{
    std::string name = plt_name_for_addr(plt_by_addr, addr);
    if (!name.empty()) return name;

    for (uint64_t delta = 0; delta < 16 && delta <= addr; ++delta)
    {
        auto it = syms_by_addr.find(addr - delta);
        if (it != syms_by_addr.end() && ends_with(it->second->name, "@plt")) return it->second->name;
    }

    return "";
}

std::vector<std::string> run_addr2line_batch(const std::string& file, const std::vector<uint64_t>& addrs)
{
    std::vector<std::string> lines;
    if (addrs.empty()) return lines;

    std::ostringstream cmd;
    cmd << "addr2line -a -f -e " << shell_quote(file);
    for (uint64_t a : addrs)
    {
        cmd << " 0x" << std::hex << a;
    }

    FILE* p = popen(cmd.str().c_str(), "r");
    if (!p) return lines;

    char buf[4096];
    while (fgets(buf, sizeof(buf), p))
    {
        lines.emplace_back(trim(buf));
    }
    pclose(p);
    return lines;
}

std::unordered_map<uint64_t, LineInfo> map_lines_with_addr2line(
    const std::string& file,
    const std::vector<uint64_t>& addrs)
{
    std::unordered_map<uint64_t, LineInfo> out;
    if (addrs.empty()) return out;

    const std::size_t chunk = 200;
    for (std::size_t i = 0; i < addrs.size(); i += chunk)
    {
        std::size_t end = std::min(addrs.size(), i + chunk);
        std::vector<uint64_t> batch(addrs.begin() + i, addrs.begin() + end);
        auto lines = run_addr2line_batch(file, batch);
        std::size_t bi = 0;
        for (std::size_t li = 0; li + 2 < lines.size() && bi < batch.size(); li += 3, ++bi)
        {
            std::string fn = lines[li + 1];
            std::string fl = lines[li + 2];
            std::string fname = "??";
            int line = 0;

            std::size_t c = fl.rfind(':');
            if (c != std::string::npos)
            {
                fname = fl.substr(0, c);
                std::string lnum = fl.substr(c + 1);
                if (!lnum.empty() && lnum != "?") line = std::atoi(lnum.c_str());
            }
            out[batch[bi]] = LineInfo{fn, fname, line};
        }
    }
    return out;
}

} // namespace

int main(int argc, char** argv)
{
    std::string input;
    std::string outputstyle = "tab";

    for (int i = 1; i < argc; ++i)
    {
        std::string a = argv[i];
        if (a == "--outputstyle" && i + 1 < argc)
        {
            outputstyle = argv[++i];
        }
        else if (!a.empty() && a[0] != '-')
        {
            input = a;
        }
    }

    if (input.empty())
    {
        std::cerr << "Usage: objdumpallocs-capstone [--outputstyle tab|punc] <elf-file>\n";
        return 1;
    }

    auto alloc_names = build_alloc_names();

    MappedFile mf;
    if (!map_file(input, mf))
    {
        std::cerr << "Could not map input file: " << input << "\n";
        return 1;
    }

    if (mf.size < sizeof(Elf64_Ehdr))
    {
        std::cerr << "Not an ELF file\n";
        return 1;
    }

    const Elf64_Ehdr* eh = reinterpret_cast<const Elf64_Ehdr*>(mf.data);
    if (!(eh->e_ident[EI_MAG0] == ELFMAG0 && eh->e_ident[EI_MAG1] == ELFMAG1 && eh->e_ident[EI_MAG2] == ELFMAG2 && eh->e_ident[EI_MAG3] == ELFMAG3))
    {
        std::cerr << "Not an ELF file\n";
        return 1;
    }

    if (eh->e_ident[EI_CLASS] != ELFCLASS64 || eh->e_machine != EM_X86_64)
    {
        std::cerr << "Only ELF64 x86_64 currently supported\n";
        return 1;
    }

    if (eh->e_shoff == 0 || eh->e_shnum == 0)
    {
        std::cerr << "No section headers\n";
        return 1;
    }

    const Elf64_Shdr* shdrs = reinterpret_cast<const Elf64_Shdr*>(mf.data + eh->e_shoff);

    std::vector<Symbol> syms;
    load_symbols(eh, shdrs, mf.data, syms);

    std::vector<SecRange> exec_secs;
    exec_secs.reserve(eh->e_shnum);
    for (std::size_t i = 0; i < eh->e_shnum; ++i)
    {
        const Elf64_Shdr& sh = shdrs[i];
        if ((sh.sh_flags & SHF_EXECINSTR) == 0) continue;
        if (sh.sh_addr == 0 || sh.sh_size == 0) continue;
        std::string n = sec_name(eh, shdrs, i, mf.data);
        exec_secs.push_back(SecRange{sh.sh_addr, sh.sh_addr + sh.sh_size, n});
    }

    std::vector<const Symbol*> func_syms;
    std::vector<const Symbol*> zero_size_func_syms;
    std::unordered_map<uint64_t, const Symbol*> syms_by_addr;
    func_syms.reserve(syms.size());
    zero_size_func_syms.reserve(syms.size());
    syms_by_addr.reserve(syms.size());

    for (const auto& s : syms)
    {
        if (s.is_func && s.is_defined)
        {
            if (s.size > 0) func_syms.push_back(&s);
            else zero_size_func_syms.push_back(&s);
        }
        if (s.is_defined && !s.name.empty())
        {
            syms_by_addr.emplace(s.addr, &s);
        }
    }

    auto by_addr = [](const Symbol* lhs, const Symbol* rhs) {
        return lhs->addr < rhs->addr;
    };
    std::stable_sort(func_syms.begin(), func_syms.end(), by_addr);
    std::stable_sort(zero_size_func_syms.begin(), zero_size_func_syms.end(), by_addr);

    std::unordered_map<uint64_t, std::string> reloc_by_va;
    std::unordered_map<SiteKey, std::string, SiteKeyHash> reloc_by_site;
    load_relocations(eh, shdrs, mf.data, reloc_by_va, reloc_by_site);
    auto plt_by_addr = load_plt_symbol_map(eh, shdrs, mf.data, reloc_by_va);

    csh handle = 0;
    if (cs_open(CS_ARCH_X86, CS_MODE_64, &handle) != CS_ERR_OK)
    {
        std::cerr << "Capstone init failed\n";
        return 1;
    }
    cs_option(handle, CS_OPT_DETAIL, CS_OPT_ON);

    std::vector<CallSite> calls;

    for (std::size_t si = 0; si < eh->e_shnum; ++si)
    {
        const Elf64_Shdr& sh = shdrs[si];
        if ((sh.sh_flags & SHF_EXECINSTR) == 0) continue;
        if (sh.sh_type != SHT_PROGBITS) continue;
        if (sh.sh_size == 0) continue;
        if (sh.sh_offset + sh.sh_size > mf.size) continue;

        const uint8_t* code = mf.data + sh.sh_offset;
        uint64_t base = sh.sh_addr;

        cs_insn* insn = cs_malloc(handle);
        if (!insn) continue;

        const uint8_t* p = code;
        size_t remaining = sh.sh_size;
        uint64_t addr = base;
        while (remaining > 0)
        {
            if (!cs_disasm_iter(handle, &p, &remaining, &addr, insn))
            {
                ++p;
                --remaining;
                ++addr;
                continue;
            }

            bool is_call = cs_insn_group(handle, insn, CS_GRP_CALL);
            bool is_jmp = cs_insn_group(handle, insn, CS_GRP_JUMP);
            if (!is_call && !is_jmp) continue;

            uint64_t insn_addr = insn->address;
            uint64_t target = 0;
            bool target_is_imm = false;
            bool has_imm_target = false;
            bool has_nonimm_target = false;
            const cs_x86& x86 = insn->detail->x86;
            
            if (x86.op_count == 1 && x86.operands[0].type == X86_OP_IMM)
            {
                target = x86.operands[0].imm;
                has_imm_target = true;
            }
            else {
                for (uint8_t oi = 0; oi < x86.op_count; ++oi)
                {
                    if (x86.operands[oi].type == X86_OP_MEM || x86.operands[oi].type == X86_OP_REG)
                    {
                        has_nonimm_target = true;
                        break;
                    }
                }
            }

            std::string callee;

            auto itva = reloc_by_va.find(insn_addr);
            if (itva != reloc_by_va.end()) callee = itva->second;

            if (callee.empty())
            {
                SiteKey k{static_cast<uint32_t>(si), insn_addr - base};
                auto itso = reloc_by_site.find(k);
                if (itso != reloc_by_site.end()) callee = itso->second;
            }

            if (callee.empty() && has_imm_target)
            {
                const Symbol* s = find_symbol_exact(syms_by_addr, target);
                if (s) callee = s->name;
            }

            if (callee.empty() && has_imm_target)
            {
                auto itplt = plt_by_addr.find(target);
                if (itplt != plt_by_addr.end()) callee = itplt->second;
            }

            bool is_alloc_match = false;
            if (!callee.empty())
            {
                std::string base_name = strip_at_version(callee);
                is_alloc_match = (alloc_names.find(base_name) != alloc_names.end());
            }

            if (!is_alloc_match && !has_nonimm_target) continue;

            calls.push_back(CallSite{insn_addr, insn_addr + insn->size});
        }

        cs_free(insn, 1);
    }

    cs_close(&handle);

    std::vector<uint64_t> ret_addrs;
    ret_addrs.reserve(calls.size());
    for (const auto& c : calls) ret_addrs.push_back(c.return_addr);

    auto line_map = map_lines_with_addr2line(input, ret_addrs);
    SourceCache source_cache;

    std::vector<OutputRec> out;
    out.reserve(calls.size());
    for (const auto& c : calls)
    {
        std::string secn = section_name_for_addr(exec_secs, c.call_addr);
        std::string sym = "??";
        uint64_t off = 0;
        std::string p = plt_name_for_addr(plt_by_addr, syms_by_addr, c.call_addr);

        if (!p.empty())
        {
            std::string n = strip_at_version(p);
            sym = n.empty() ? "??" : (n + "@plt");
        }
        else if (secn == ".plt")
        {
            sym = secn;
        }
        else
        {
            const Symbol* fs = find_function_for_addr(func_syms, zero_size_func_syms, c.call_addr);
            if (fs)
            {
                sym = fs->name;
                off = c.return_addr - fs->addr;
            }
        }

        if (sym == "??")
        {
            if (secn == ".init" || secn == ".plt.got" || secn == ".plt.sec" || secn == ".fini")
            {
                sym = secn;
            }
        }

        auto it = line_map.find(c.call_addr);
        std::string file = "??";
        int line = 0;
        std::string source;
        std::string token = "$FAILED$";
        if (it != line_map.end())
        {
            if (sym == "??" && !it->second.func.empty() && it->second.func != "??")
            {
                sym = it->second.func;
            }
            file = it->second.file;
            line = it->second.line;
            if (line <= 0) file = "??";
            source = collapse_ws(source_cache.get_line(file, line));
            if (!source.empty()) token = extract_alloc_token(source);
        }

        std::ostringstream off_ss;
        off_ss << "0x" << std::hex << off;

        out.push_back(OutputRec{
            sym,
            c.return_addr,
            off_ss.str(),
            file,
            line,
            line + 1,
            token,
            source
        });
    }

    std::stable_sort(out.begin(), out.end(), [](const OutputRec& a, const OutputRec& b) {
        if (a.filename != b.filename) return a.filename < b.filename;
        return a.line < b.line;
    });

    for (const auto& r : out)
    {
        if (outputstyle == "punc")
        {
            std::cout << "<" << r.return_sym << "+" << r.return_off << "> @"
                      << r.filename << ":" << std::setw(6) << std::setfill('0') << r.line
                      << "\t" << r.token << "\n";
        }
        else
        {
            std::cout << r.return_sym << "\t"
                      << "0x" << std::hex << std::setw(16) << std::setfill('0') << r.return_addr << std::dec << "\t"
                      << r.filename << "\t"
                      << std::setw(6) << std::setfill('0') << r.line << "\t"
                      << std::setw(6) << std::setfill('0') << r.line_end << "\t"
                      << r.token << "\t"
                      << r.source << "\n";
        }
    }

    return 0;
}
