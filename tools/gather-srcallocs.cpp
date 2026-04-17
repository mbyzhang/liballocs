#include <algorithm>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fcntl.h>
#include <fstream>
#include <gelf.h>
#include <iostream>
#include <libelf.h>
#include <regex>
#include <set>
#include <sstream>
#include <string>
#include <unistd.h>
#include <vector>

#include <boost/algorithm/string.hpp>
#include <dwarfpp/lib.hpp>
#include <fileno.hpp>

using std::cerr;
using std::cout;
using std::endl;
using std::string;
using std::vector;

static int verbose_out = false;

static string dirname_of(const string& path)
{
    const auto slash = path.find_last_of('/');
    if (slash == string::npos) return ".";
    if (slash == 0) return "/";
    return path.substr(0, slash);
}

static string realpath_or_self(const string& path)
{
    char *resolved = ::realpath(path.c_str(), nullptr);
    if (!resolved) return path;
    string out(resolved);
    std::free(resolved);
    return out;
}

static vector<string> split_lines_keep_nonempty(const string& s)
{
    vector<string> lines;
    std::istringstream in(s);
    string line;
    while (std::getline(in, line))
    {
        if (!line.empty() && line.back() == '\r') line.pop_back();
        if (!line.empty()) lines.push_back(line);
    }
    return lines;
}

static bool is_integer_field(const string& field)
{
    string trimmed = boost::algorithm::trim_copy(field);
    if (trimmed.empty()) return false;
    return std::all_of(trimmed.begin(), trimmed.end(), [](unsigned char ch) {
        return std::isdigit(ch);
    });
}

static string pad_field_if_number(const string& field)
{
    if (!is_integer_field(field)) return field;

    string trimmed = boost::algorithm::trim_copy(field);
    unsigned long value = 0;
    try
    {
        value = std::stoul(trimmed);
    }
    catch (...)
    {
        return field;
    }

    char buf[64];
    std::snprintf(buf, sizeof buf, "%06lu", value);
    return string(buf);
}

static string pad_numbers_per_field(const string& line)
{
    vector<string> fields;
    boost::split(fields, line, boost::is_any_of("\t"));
    for (auto& f : fields) f = pad_field_if_number(f);
    return boost::algorithm::join(fields, "\t");
}

static vector<string> read_unique_objects(const string& all_obj_allocs_file)
{
    FILE *fp = std::fopen(all_obj_allocs_file.c_str(), "r");
    if (!fp) return {};

    std::set<string> objs;
    char *line = nullptr;
    size_t cap = 0;
    while (getline(&line, &cap, fp) != -1)
    {
        string s(line);
        if (!s.empty() && s.back() == '\n') s.pop_back();
        auto tab = s.find('\t');
        string obj = (tab == string::npos) ? s : s.substr(0, tab);
        if (!obj.empty()) objs.insert(obj);
    }

    if (line) std::free(line);
    std::fclose(fp);
    return vector<string>(objs.begin(), objs.end());
}

struct CuInfo
{
    unsigned language_num;
    string language_fullstr;
    string sourcepath;
    string fname;
    string compdir;
};

static string dwarf_language_desc(unsigned lang)
{
    std::ostringstream ss;
    ss << "DW_LANG(" << lang << ")";
    return ss.str();
}

static vector<CuInfo> get_cu_infos(const string& obj)
{
    using dwarf::core::compile_unit_die;
    using dwarf::core::iterator_sibs;
    using dwarf::core::root_die;

    std::ifstream infstream(obj);
    if (!infstream) return {};

    vector<CuInfo> infos;
    root_die root(fileno(infstream));

    auto cus = root.begin().children();
    for (iterator_sibs<compile_unit_die> i_cu = cus.first;
         i_cu != cus.second; ++i_cu)
    {
        string fname = i_cu->get_name() ? *i_cu->get_name() : "";
        string compdir = i_cu->get_comp_dir() ? *i_cu->get_comp_dir() : "";
        unsigned lang = i_cu->get_language();

        string sourcepath;
        if (!fname.empty() && fname[0] == '/') sourcepath = fname;
        else if (!compdir.empty() && !fname.empty()) sourcepath = compdir + "/" + fname;
        else sourcepath = fname;

        infos.push_back(CuInfo{lang, dwarf_language_desc(lang), sourcepath, fname, compdir});
    }

    return infos;
}

static string read_elf_section_binary_from(const string& obj, const string& section_name)
{
    string out;

    if (elf_version(EV_CURRENT) == EV_NONE) return out;

    int fd = open(obj.c_str(), O_RDONLY);
    if (fd < 0) return out;

    Elf *elf = elf_begin(fd, ELF_C_READ, nullptr);
    if (!elf)
    {
        close(fd);
        return out;
    }

    size_t shstrndx = 0;
    if (elf_getshdrstrndx(elf, &shstrndx) != 0)
    {
        elf_end(elf);
        close(fd);
        return out;
    }

    for (Elf_Scn *scn = elf_nextscn(elf, nullptr); scn != nullptr; scn = elf_nextscn(elf, scn))
    {
        GElf_Shdr shdr;
        if (!gelf_getshdr(scn, &shdr)) continue;

        const char *name = elf_strptr(elf, shstrndx, shdr.sh_name);
        if (!name) continue;
        if (section_name != name) continue;

        for (Elf_Data *data = elf_getdata(scn, nullptr); data != nullptr; data = elf_getdata(scn, data))
        {
            if (!data->d_buf || data->d_size == 0) continue;
            out.append(static_cast<const char *>(data->d_buf), static_cast<size_t>(data->d_size));
        }
    }

    elf_end(elf);
    close(fd);
    return out;
}

static bool has_debug_info_section(const string& obj)
{
    if (elf_version(EV_CURRENT) == EV_NONE) return false;

    int fd = open(obj.c_str(), O_RDONLY);
    if (fd < 0) return false;

    bool found = false;
    Elf *elf = elf_begin(fd, ELF_C_READ, nullptr);
    if (elf)
    {
        size_t shstrndx = 0;
        if (elf_getshdrstrndx(elf, &shstrndx) == 0)
        {
            for (Elf_Scn *scn = elf_nextscn(elf, nullptr); scn != nullptr; scn = elf_nextscn(elf, scn))
            {
                GElf_Shdr shdr;
                if (!gelf_getshdr(scn, &shdr)) continue;
                const char *name = elf_strptr(elf, shstrndx, shdr.sh_name);
                if (!name) continue;
                if (string(name) == ".debug_info" && shdr.sh_size > 0)
                {
                    found = true;
                    break;
                }
            }
        }
        elf_end(elf);
    }

    close(fd);
    return found;
}

static string read_debuglink(const string& obj)
{
    const string payload = read_elf_section_binary_from(obj, ".gnu_debuglink");
    if (payload.empty()) return "";

    const auto nul = payload.find('\0');
    if (nul == string::npos) return "";
    return payload.substr(0, nul);
}

static size_t align4(size_t v)
{
    return (v + 3u) & ~static_cast<size_t>(3u);
}

static string read_build_id(const string& obj)
{
    const string payload = read_elf_section_binary_from(obj, ".note.gnu.build-id");
    if (payload.size() < 12) return "";

    size_t off = 0;
    while (off + 12 <= payload.size())
    {
        uint32_t namesz = 0;
        uint32_t descsz = 0;
        uint32_t type = 0;
        std::memcpy(&namesz, payload.data() + off, sizeof(namesz));
        std::memcpy(&descsz, payload.data() + off + 4, sizeof(descsz));
        std::memcpy(&type, payload.data() + off + 8, sizeof(type));
        off += 12;

        if (off + namesz > payload.size()) break;
        const char *name_ptr = payload.data() + off;
        off += align4(namesz);

        if (off + descsz > payload.size()) break;
        const unsigned char *desc_ptr =
            reinterpret_cast<const unsigned char *>(payload.data() + off);
        off += align4(descsz);

        const bool name_is_gnu = (namesz >= 3 && std::memcmp(name_ptr, "GNU", 3) == 0);
        if (name_is_gnu && type == NT_GNU_BUILD_ID)
        {
            static const char hex[] = "0123456789abcdef";
            string out;
            out.reserve(descsz * 2);
            for (uint32_t i = 0; i < descsz; ++i)
            {
                unsigned char b = desc_ptr[i];
                out.push_back(hex[(b >> 4) & 0x0f]);
                out.push_back(hex[b & 0x0f]);
            }
            return out;
        }
    }

    return "";
}

static string resolve_debug_file_for(const string& obj)
{
    if (has_debug_info_section(obj)) return obj;

    const string canon_obj = realpath_or_self(obj);

    const string debuglink = read_debuglink(canon_obj);
    if (!debuglink.empty())
    {
        const string obj_dir = dirname_of(canon_obj);
        const string c1 = obj_dir + "/.debug/" + debuglink;
        if (has_debug_info_section(c1)) return c1;

        const string c2 = "/usr/lib/debug" + obj_dir + "/" + debuglink;
        if (has_debug_info_section(c2)) return c2;
    }

    const string build_id = read_build_id(canon_obj);
    if (build_id.size() >= 3)
    {
        const string c3 = "/usr/lib/debug/.build-id/" + build_id.substr(0, 2) +
            "/" + build_id.substr(2) + ".debug";
        if (has_debug_info_section(c3)) return c3;
    }

    return obj;
}

static bool read_file_contents(const string& path, string& out)
{
    std::ifstream in(path);
    if (!in) return false;

    std::ostringstream ss;
    ss << in.rdbuf();
    out = ss.str();
    return true;
}

static string rewrite_cu_allocspath(const string& sourcepath, const string& extension)
{
    std::smatch m;

    std::regex cil_re("^(.*)\\.cil\\.[ci]$");
    if (std::regex_match(sourcepath, m, cil_re) && m.size() > 1)
    {
        return m[1].str() + ".i." + extension;
    }

    std::regex c_re("^(.*)\\.c$");
    if (std::regex_match(sourcepath, m, c_re) && m.size() > 1)
    {
        return m[1].str() + ".i." + extension;
    }

    return "";
}

static vector<string> gather_from_c_translation_unit(const string& sourcepath, const string& extension)
{
    vector<string> lines;
    const string allocspath = rewrite_cu_allocspath(sourcepath, extension);

    cerr << "Warning: cu_allocspath is " << allocspath << endl;

    if (allocspath.empty()) return lines;

    string content;
    if (!read_file_contents(allocspath, content))
    {
        cerr << "Warning: missing expected allocs file (" << allocspath
             << ") for source file: " << sourcepath << endl;
        return lines;
    }

    return split_lines_keep_nonempty(content);
}

static bool is_c_language(unsigned lang)
{
    return lang == 1u || lang == 2u || lang == 12u || lang == 29u;
}

int main(int argc, char **argv)
{
    if (argc != 2)
    {
        std::cerr << "Usage: " << argv[0] << " <all_obj_allocs_file>" << std::endl;
        return 1;
    }

    const string exe_path = argv[0];
    const auto slash = exe_path.find_last_of('/');
    const string exe_name = (slash == string::npos) ? exe_path : exe_path.substr(slash + 1);

    std::regex name_re("^gather-src(.*?)(?:\\.sh)?$");
    std::smatch m;
    if (!std::regex_match(exe_name, m, name_re) || m.size() < 2)
    {
        std::cerr << "Did not understand our name (" << argv[0] << ")" << std::endl;
        return 1;
    }

    const string our_name_frag = m[1].str();
    const string extension = (our_name_frag == "memacc") ? "memacc" : "allocs";
    const string all_obj_allocs_file = argv[1];

    if (getenv("GATHER_SRCALLOCS_VERBOSE"))
    {
        verbose_out = atoi(getenv("GATHER_SRCALLOCS_VERBOSE"));
    }

    if (verbose_out) std::cerr << "Hello" << std::endl;

    vector<string> aggregate_lines;
    const auto objs = read_unique_objects(all_obj_allocs_file);
    for (const auto& obj : objs)
    {
        if (verbose_out) std::cerr << "Saw line " << obj << std::endl;

        const string section = ".allocs_src" + our_name_frag;
        const string embedded_info = read_elf_section_binary_from(obj, section);
        if (verbose_out) std::cerr << "Embedded info is `" << embedded_info << "'" << std::endl;

        const string dwarf_obj = resolve_debug_file_for(obj);
        const auto cu_infos = get_cu_infos(dwarf_obj);
        for (const auto& cu : cu_infos)
        {
            if (is_c_language(cu.language_num))
            {
                auto lines = gather_from_c_translation_unit(cu.sourcepath, extension);
                aggregate_lines.insert(aggregate_lines.end(), lines.begin(), lines.end());
            }
            else
            {
                std::cerr << "Warning: could not gather source-level allocs for unknown language: "
                          << cu.language_fullstr << " (" << cu.language_num << ")" << std::endl;
            }
        }

        auto embedded_lines = split_lines_keep_nonempty(embedded_info);
        aggregate_lines.insert(aggregate_lines.end(), embedded_lines.begin(), embedded_lines.end());
    }

    vector<string> normalized;
    normalized.reserve(aggregate_lines.size());
    for (const auto& line : aggregate_lines) normalized.push_back(pad_numbers_per_field(line));

    std::sort(normalized.begin(), normalized.end(), [](const string& a, const string& b) {
        vector<string> fa;
        vector<string> fb;
        boost::split(fa, a, boost::is_any_of("\t"));
        boost::split(fb, b, boost::is_any_of("\t"));

        const string a1 = fa.size() > 0 ? fa[0] : "";
        const string b1 = fb.size() > 0 ? fb[0] : "";
        if (a1 != b1) return a1 < b1;

        const string a2 = fa.size() > 1 ? fa[1] : "";
        const string b2 = fb.size() > 1 ? fb[1] : "";
        if (a2 != b2) return a2 < b2;

        return a < b;
    });

    normalized.erase(std::unique(normalized.begin(), normalized.end()), normalized.end());

    for (const auto& line : normalized) cout << line << '\n';
    return 0;
}
