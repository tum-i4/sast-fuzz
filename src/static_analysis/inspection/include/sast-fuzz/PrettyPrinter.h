#ifndef PI_PRETTYPRINTER_H
#define PI_PRETTYPRINTER_H

#include <map>
#include <sast-fuzz/FuncInfo.h>
#include <sast-fuzz/IO.h>
#include <set>
#include <string>
#include <vector>

namespace sfi {

class Printer {
  public:
    virtual std::string format(std::vector<FuncInfo> &funcInfos, std::map<BBId, std::set<BBId>> &icfgInfos) = 0;

    void
    printToFile(std::string &filepath, std::vector<FuncInfo> &funcInfos, std::map<BBId, std::set<BBId>> &icfgInfos) {
        IO::writeFile(filepath, format(funcInfos, icfgInfos));
    }
};

class JSONPrinter : public Printer {
  public:
    std::string format(std::vector<FuncInfo> &funcInfos, std::map<BBId, std::set<BBId>> &icfgInfos) override;
};

}  // namespace sfi

#endif  // PI_PRETTYPRINTER_H
