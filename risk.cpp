#include <iostream>
#include <string>
#include <fstream>
#include <sstream>
#include <vector>
#include <unordered_map>
#include <stack>
#include <cmath>
#include <algorithm>
#include <iomanip>
#include <queue>
#include <climits>
#include <bitset>
#include <ctime>

using namespace std;

const int mem_size = 0x50000;

unsigned long long PC = 0;
long regs[32];
unsigned char mem[mem_size];
int cacheenable = 0;
unordered_map<string, int> lMap;
vector<string> lines;
vector<int> breakpoints;
stack<pair<string, int>> call_stack;
string execname;

void log_cache_simulation(const string &operation, uint32_t address, int set, bool hit, uint32_t tag, bool dirty)
{
    static ofstream outfile;
    static bool file_opened = false;

    if (!file_opened)
    {
        size_t last_dot = execname.find_last_of(".");
        string filename = execname.substr(0, last_dot) + ".output";
        outfile.open(filename, ios::out);
        file_opened = true;
    }

    stringstream ss;
    ss << (operation == "R" ? "R: " : "W: ");
    ss << "Address: 0x" << hex << address << ", ";
    ss << "Set: 0x" << hex << set << ", ";
    ss << (hit ? "Hit, " : "Miss, ");
    ss << "Tag: 0x" << hex << tag << ", ";
    ss << (dirty ? "Dirty" : "Clean") << endl;

    outfile << ss.str();
    outfile.flush();
}

int t;
class Cache
{
public:
    int size, block, assoc, hits, miss, repl, writep;
    unsigned char **data;
    int **addrs;
    char **durty;
    int **timestamps;
    queue<int> *fifo;

    Cache(int size, int block, int assoc, int repl, int writep)
        : size(size), block(block), assoc(assoc), hits(0), miss(0), repl(repl), writep(writep)
    {
        int lines = size / (block * assoc);

        data = new unsigned char *[lines];
        for (int i = 0; i < lines; i++)
            data[i] = new unsigned char[block * assoc];

        addrs = new int *[lines];
        for (int i = 0; i < lines; i++)
        {
            addrs[i] = new int[assoc];
            for (int j = 0; j < assoc; j++)
            {
                addrs[i][j] = -1;
            }
        }
        durty = new char *[lines];
        for (int i = 0; i < lines; i++)
            durty[i] = new char[assoc];

        timestamps = new int *[lines];
        for (int i = 0; i < lines; i++)
        {
            timestamps[i] = new int[assoc];
            for (int j = 0; j < assoc; j++)
            {
                timestamps[i][j] = 0;
            }
        }
        fifo = new queue<int>[lines];
    }

    long long int read(int addr, int byte)
    {
        t++;
        int indexSize = (int)log2(size / (block * assoc));
        int offset = (int)log2(block);
        int ind = (addr >> (offset)) & ((1 << indexSize) - 1);
        int intag = addr >> (offset + indexSize);
        offset = (addr & ((1 << offset) - 1));

        for (int i = 0; i < assoc; i++)
        {
            if (addrs[ind][i] == intag)
            {
                hits++;
                if (repl == 0)
                {
                    timestamps[ind][i] = t;
                }
                long long int result = 0;
                for (int j = 0; j < byte; j++)
                {
                    result |= ((long long int)data[ind][i * block + offset + j] << (8 * j));
                }
                log_cache_simulation("R", addr, ind, true, intag, durty[ind][i]);
                return result;
            }
        }

        int i;
        bool flag = false;
        for (i = 0; i < assoc; i++)
        {
            if (addrs[ind][i] == -1)
            {
                flag = true;
                break;
            }
        }

        miss++;
        log_cache_simulation("R", addr, ind, false, intag, false);

        if (flag)
        {
            int block_start = addr - offset;
            for (int j = 0; j < block; j++)
            {
                data[ind][i * block + j] = mem[block_start + j];
            }
            addrs[ind][i] = intag;
            timestamps[ind][i] = t;
            durty[ind][i] = 0;

            long long int result = 0;
            for (int j = 0; j < byte; j++)
            {
                result |= ((long long int)data[ind][i * block + offset + j] << (8 * j));
            }
            if (repl == 0)
            {
                timestamps[ind][i] = t;
            }
            else if (repl == 1)
            {
                fifo[ind].push(i);
            }
            return result;
        }

        int victim = 0;
        if (repl == 0)
        {
            int min_time = INT_MAX;
            for (int i = 0; i < assoc; i++)
            {
                if (timestamps[ind][i] < min_time)
                {
                    min_time = timestamps[ind][i];
                    victim = i;
                }
            }
        }
        else if (repl == 1)
        {
            victim = fifo[ind].front();
            fifo[ind].pop();
            fifo[ind].push(victim);
        }
        else
        {

            victim = rand() % assoc;
        }

        if (durty[ind][victim])
        {
            int victim_addr = addrs[ind][victim] << (offset + indexSize);
            for (int i = 0; i < block; i++)
            {
                mem[victim_addr + i] = data[ind][victim * block + i];
            }
        }

        int block_start = addr - offset;
        for (int i = 0; i < block; i++)
        {
            data[ind][victim * block + i] = mem[block_start + i];
        }
        addrs[ind][victim] = intag;
        timestamps[ind][victim] = t;
        durty[ind][victim] = 0;

        long long int result = 0;
        for (int i = 0; i < byte; i++)
        {
            result |= ((long long int)data[ind][victim * block + offset + i] << (8 * i));
        }
        return result;
    }

    void write(int addr, long long int val, int byte)
    {
        t++;
        int indexSize = (int)log2(size / (block * assoc));
        int offset = (int)log2(block);
        int line = (addr >> (offset)) & ((1 << indexSize) - 1);
        int tag = addr >> (offset + indexSize);
        offset = (addr & ((1 << offset) - 1) );

        for (int i = 0; i < assoc; i++)
        {
            if (addrs[line][i] == tag)
            {
                hits++;
                if (repl == 0)
                {
                    timestamps[line][i] = t;
                }
                for (int j = 0; j < byte; j++)
                {
                    data[line][i * block + offset + j] = (val >> (8 * j)) & 0xFF;
                }
                if (writep)
                {
                    durty[line][i] = 1;
                }
                else
                {
                    for (int j = 0; j < byte; j++)
                    {
                        mem[addr + j] = (val >> (8 * j)) & 0xFF;
                    }
                }
                log_cache_simulation("W", addr, line, true, tag, durty[line][i]);
                return;
            }
        }

        miss++;

        if (writep)
        {
            log_cache_simulation("W", addr, line, false, tag, true);
            int i;
            bool flag = false;
            for (i = 0; i < assoc; i++)
            {
                if (addrs[line][i] == -1)
                {
                    flag = true;
                    break;
                }
            }

            if (flag)
            {
                int block_start = addr - offset;
                for (int j = 0; j < block; j++)
                {
                    data[line][i * block + j] = mem[block_start + j];
                }
                addrs[line][i] = tag;
                timestamps[line][i] = t;
                durty[line][i] = 1;

                for (int j = 0; j < byte; j++)
                {
                    data[line][i * block + offset + j] = (val >> (8 * j)) & 0xFF;
                }
                if (repl == 0)
                {
                    timestamps[line][i] = t;
                }
                else if (repl == 1)
                {
                    fifo[line].push(i);
                }
                return;
            }

            int victim = 0;
            if (repl == 0)
            {
                int min_time = INT_MAX;
                for (int i = 0; i < assoc; i++)
                {
                    if (timestamps[line][i] < min_time)
                    {
                        min_time = timestamps[line][i];
                        victim = i;
                    }
                }
            }
            else if (repl == 1)
            {
                victim = fifo[line].front();
                fifo[line].pop();
                fifo[line].push(victim);
            }
            else
            {
                victim = rand() % assoc;
            }

            if (durty[line][victim])
            {
                int victim_addr = addrs[line][victim] * block;
                for (int i = 0; i < block; i++)
                {
                    mem[victim_addr + i] = data[line][victim * block + i];
                }
            }

            int block_start = addr - offset;
            for (int i = 0; i < block; i++)
            {
                data[line][victim * block + i] = mem[block_start + i];
            }

            addrs[line][victim] = tag;
            timestamps[line][victim] = t;
            durty[line][victim] = 0;

            for (int i = 0; i < byte; i++)
            {
                data[line][victim * block + offset + i] = (val >> (8 * i)) & 0xFF;
            }
        }
        else
        {
            log_cache_simulation("W", addr, line, false, tag, false);
            for (int j = 0; j < byte; j++)
            {
                mem[addr + j] = (val >> (8 * j)) & 0xFF;
            }
        }
    }
};

unordered_map<string, string>
    opMap =
        {
            {"add", "0110011"}, {"sub", "0110011"}, {"and", "0110011"}, {"or", "0110011"}, {"xor", "0110011"}, {"sll", "0110011"}, {"srl", "0110011"}, {"sra", "0110011"}, {"addi", "0010011"}, {"andi", "0010011"}, {"ori", "0010011"}, {"xori", "0010011"}, {"slli", "0010011"}, {"srli", "0010011"}, {"srai", "0010011"}, {"ld", "0000011"}, {"lw", "0000011"}, {"lh", "0000011"}, {"lb", "0000011"}, {"lwu", "0000011"}, {"lhu", "0000011"}, {"lbu", "0000011"}, {"sd", "0100011"}, {"sw", "0100011"}, {"sh", "0100011"}, {"sb", "0100011"}, {"jalr", "1100111"}, {"beq", "1100011"}, {"bne", "1100011"}, {"blt", "1100011"}, {"bge", "1100011"}, {"bltu", "1100011"}, {"bgeu", "1100011"}, {"jal", "1101111"}, {"lui", "0110111"}};

unordered_map<string, int> regMap =
    {
        {"x0", 0}, {"x1", 1}, {"x2", 2}, {"x3", 3}, {"x4", 4}, {"x5", 5}, {"x6", 6}, {"x7", 7}, {"x8", 8}, {"x9", 9}, {"x10", 10}, {"x11", 11}, {"x12", 12}, {"x13", 13}, {"x14", 14}, {"x15", 15}, {"x16", 16}, {"x17", 17}, {"x18", 18}, {"x19", 19}, {"x20", 20}, {"x21", 21}, {"x22", 22}, {"x23", 23}, {"x24", 24}, {"x25", 25}, {"x26", 26}, {"x27", 27}, {"x28", 28}, {"x29", 29}, {"x30", 30}, {"x31", 31}, {"zero", 0}, {"ra", 1}, {"sp", 2}, {"gp", 3}, {"tp", 4}, {"t0", 5}, {"t1", 6}, {"t2", 7}, {"s0", 8}, {"fp", 8}, {"s1", 9}, {"a0", 10}, {"a1", 11}, {"a2", 12}, {"a3", 13}, {"a4", 14}, {"a5", 15}, {"a6", 16}, {"a7", 17}, {"s2", 18}, {"s3", 19}, {"s4", 20}, {"s5", 21}, {"s6", 22}, {"s7", 23}, {"s8", 24}, {"s9", 25}, {"s10", 26}, {"s11", 27}, {"t3", 28}, {"t4", 29}, {"t5", 30}, {"t6", 31}};

string int_to_hex(unsigned long long num, int numBits = 32)
{
    string hex;
    char hexMap[] = {'0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F'};

    if (num == 0)
        return "0x0";

    if (num < 0)
    {
        num = pow(2, numBits) + num;
    }

    while (num)
    {
        hex = hexMap[num % 16] + hex;
        num /= 16;
    }

    if (hex.length() < numBits / 4)
        hex = string(numBits / 4 - hex.length(), '0') + hex;

    return "0x" + hex;
}

string removespace(string str)
{
    size_t start = str.find_first_not_of(" \t\n\r\f\v");
    if (start == string::npos)
        return "";
    size_t end = str.find_last_not_of(" \t\n\r\f\v");
    return str.substr(start, end - start + 1);
}

pair<int, bool> processImm(const string &imm, int numBit, int lineNum, bool isNeg)
{
    try
    {
        int val;
        if (imm.find("0x") == 0)
        {
            val = stoi(imm, nullptr, 16);
        }
        else if (imm.find("0b") == 0)
        {
            val = stoi(imm.substr(2), nullptr, 2);
        }
        else
        {
            size_t ptr;
            val = stoi(imm, &ptr);
            if (ptr != imm.length())
            {
                cerr << "Error on line " << lineNum << ": Invalid immediate value '" << imm << "'\n";
                return {0, false};
            }
        }

        int min = -pow(2, numBit - 1);
        int max = pow(2, numBit - 1) - 1;

        if (numBit == 20)
        {
            min = 0;
            max = pow(2, 32 - 1) - 1;
            val = val << 12;
            return {val, true};
        }

        if (isNeg)
        {
            min = 0;
            max = pow(2, numBit) - 1;
        }

        if (isNeg && val < 0)
        {
            cerr << "Error on line " << lineNum << ": Immediate value '" << imm << "' is negative\n";
            return {0, false};
        }
        if (val < min || val > max)
        {
            cerr << "Error on line " << lineNum << ": Immediate value '" << imm << "' does not fit in " << numBit << " bits\n";
            return {0, false};
        }

        return {val, true};
    }
    catch (const invalid_argument &e)
    {
        cerr << "Error on line " << lineNum << ": Invalid immediate value '" << imm << "'\n";
        return {0, false};
    }
    catch (const out_of_range &e)
    {
        cerr << "Error on line " << lineNum << ": Immediate value '" << imm << "' does not fit in 32 bits\n";
        return {0, false};
    }
}

pair<long int, bool> dword_to_int(string dword, int lineNum)
{
    try
    {
        size_t ptr;
        long int val = stoll(dword, &ptr);
        if (ptr != dword.length())
        {
            cerr << "Error on line " << lineNum << ": Invalid immediate value '" << dword << "'\n";
            return {0, false};
        }
        return {val, true};
    }
    catch (const invalid_argument &e)
    {
        cerr << "Error: Invalid immediate value '" << dword << "'\n";
        return {0, false};
    }
    catch (const out_of_range &e)
    {
        cerr << "Error: Immediate value '" << dword << "' does not fit in 64 bits\n";
        return {0, false};
    }
}

void checkReg(const string &reg)
{
    if (regMap.find(reg) == regMap.end())
    {
        cerr << "Error on line " << PC << ": Unknown register '" << reg << "'\n";
        return;
    }
}

vector<string> parse(string s)
{
    vector<string> tree;
    int i = 0;
    string temp = "";
    while (i < s.length())
    {
        while (s[i] != ' ' && s[i] != ',' && i < s.length())
        {
            temp += s[i];
            i++;
        }
        if (temp != "")
        {
            tree.push_back(temp);
            temp = "";
        }
        i++;
    }

    return tree;
}

Cache *myCache = nullptr;

void execute(const string &instruction)
{
    string cmd = "";
    string line = instruction;
    vector<string> args;
    string temp = "";
    int i = 0, j = 0;
    while (line[i] == ' ' || line[i] == ',' || line[i] == '(' || line[i] == ')')
    {
        i++;
        if (line[i] == '(')
        {
            j++;
        }
        if (line[i] == ')')
        {
            j--;
        }
    }
    while (line[i] != ' ' && line[i] != ',' && line[i] != '(' && line[i] != ')')
    {
        temp += line[i];
        i++;
        if (line[i] == '(')
        {
            j++;
        }
        if (line[i] == ')')
        {
            j--;
        }
    }
    cmd = temp;
    for (; i < line.length(); i++)
    {
        temp = "";
        while (line[i] != ',' && line[i] != ' ' && line[i] != '(' && line[i] != ')' && i < line.length())
        {
            temp += line[i];
            i++;
        }
        if (line[i] == '(')
        {
            j++;
        }
        if (line[i] == ')')
        {
            j--;
        }
        if (temp == "")
            continue;
        args.push_back(temp);
    }

    if (opMap[cmd] == opMap["add"])
    {
        if (args.size() != 3)
        {
            cerr << "Error on line " << PC + 1 << ": Instruction " << cmd << " [rd] [rs1] [rs2] expects 3 arguments but got " << args.size() << "\n";
            return;
        }

        checkReg(args[0]);
        checkReg(args[1]);
        checkReg(args[2]);

        int rd = regMap[args[0]];
        int rs1 = regMap[args[1]];
        int rs2 = regMap[args[2]];

        if (cmd == "add")
            regs[rd] = regs[rs1] + regs[rs2];
        else if (cmd == "sub")
            regs[rd] = regs[rs1] - regs[rs2];
        else if (cmd == "and")
            regs[rd] = regs[rs1] & regs[rs2];
        else if (cmd == "or")
            regs[rd] = regs[rs1] | regs[rs2];
        else if (cmd == "xor")
            regs[rd] = regs[rs1] ^ regs[rs2];
        else if (cmd == "sll")
            regs[rd] = regs[rs1] << regs[rs2];
        else if (cmd == "srl")
            regs[rd] = regs[rs1] >> regs[rs2];
        else if (cmd == "sra")
            regs[rd] = regs[rs1] >> regs[rs2];
        cout << "Executed: " << instruction << "; PC = " << int_to_hex(PC * 4) << "\n";

        PC++;
        call_stack.top().second = PC;
    }

    else if (cmd == "jalr")
    {
        if (args.size() != 3)
        {
            cerr << "Error on line " << PC + 1 << ": Instruction " << cmd << " [rd] [rs1] [imm(12)] expects 3 arguments but got " << args.size() << "\n";
            return;
        }
        checkReg(args[0]);
        checkReg(args[2]);
        int rd = regMap[args[0]];
        int rs1 = regMap[args[2]];
        if (!processImm(args[1], 12, PC, false).second)
            return;
        int imm = processImm(args[1], 12, PC, false).first;
        regs[rd] = (PC + 1) * 4;
        cout << "Executed: " << instruction << "; PC = " << int_to_hex(PC * 4) << "\n";
        PC = regs[rs1] / 4 + imm;

        if (!call_stack.empty())
        {
            call_stack.pop();
        }
    }

    else if (opMap[cmd] == opMap["addi"])
    {
        if (args.size() != 3)
        {
            cerr << "Error on line " << PC + 1 << ": Instruction " << cmd << " [rd] [rs1] [imm(12)] expects 3 arguments but got " << args.size() << "\n";
            return;
        }

        checkReg(args[0]);
        checkReg(args[1]);

        int rd = regMap[args[0]];
        int rs1 = regMap[args[1]];
        int imm;

        if (cmd[0] == 's')
        {
            if (!processImm(args[2], 6, PC, true).second)
                return;
            imm = processImm(args[2], 6, PC, true).first;
            if (cmd == "slli")
                regs[rd] = regs[rs1] << imm;
            else if (cmd == "srli")
                regs[rd] = regs[rs1] >> imm;
            else if (cmd == "srai")
                regs[rd] = unsigned(regs[rs1]) >> imm;
            cout << "Executed: " << instruction << "; PC = " << int_to_hex(PC * 4) << "\n";
            PC++;
            call_stack.top().second = PC;
        }

        else
        {
            if (!processImm(args[2], 12, PC, false).second)
                return;
            imm = processImm(args[2], 12, PC, false).first;
            if (cmd == "addi")
                regs[rd] = regs[rs1] + imm;
            else if (cmd == "andi")
                regs[rd] = regs[rs1] & imm;
            else if (cmd == "ori")
                regs[rd] = regs[rs1] | imm;
            else if (cmd == "xori")
                regs[rd] = regs[rs1] ^ imm;
            cout << "Executed: " << instruction << "; PC = " << int_to_hex(PC * 4) << "\n";
            PC++;
            call_stack.top().second = PC;
        }
    }

    else if (opMap[cmd] == opMap["ld"])
    {
        if (args.size() != 3)
        {
            cerr << "Error on line " << PC + 1 << ": Instruction " << cmd << " [rd] [imm(12)] [rs1] expects 3 arguments but got " << args.size() << "\n";
            return;
        }

        checkReg(args[0]);
        checkReg(args[2]);

        int rd = regMap[args[0]];
        if (!processImm(args[1], 12, PC, false).second)
            return;
        int adr = processImm(args[1], 12, PC, false).first;
        adr += regs[regMap[args[2]]];

        if (!cacheenable)
        {
            if (cmd == "ld")
            {
                regs[rd] = 0;
                for (int i = 0; i < 8; i++)
                {
                    regs[rd] += (long long)mem[adr + i] << (8 * i);
                }
            }
            else if (cmd == "lw")
            {
                regs[rd] = 0;
                for (int i = 0; i < 4; i++)
                {
                    regs[rd] += (long long)mem[adr + i] << (8 * i);
                }
                if (regs[rd] & (1 << 31))
                {
                    regs[rd] = regs[rd] | 0xFFFFFFFF00000000;
                }
            }
            else if (cmd == "lh")
            {
                regs[rd] = mem[adr] + ((long long)mem[adr + 1] << 8);
                if (regs[rd] & (1 << 15))
                {
                    regs[rd] = regs[rd] | 0xFFFFFFFFFFFF0000;
                }
            }
            else if (cmd == "lb")
            {
                regs[rd] = mem[adr];
                if (regs[rd] & (1 << 7))
                {
                    regs[rd] = regs[rd] | 0xFFFFFFFFFFFFFF00;
                }
            }
            else if (cmd == "lwu")
            {
                regs[rd] = 0;
                for (int i = 0; i < 4; i++)
                {
                    regs[rd] += (long long)mem[adr + i] << (8 * i);
                }
            }
            else if (cmd == "lhu")
            {
                regs[rd] = mem[adr] + ((long long)mem[adr + 1] << 8);
            }
            else if (cmd == "lbu")
            {
                regs[rd] = mem[adr];
            }
        }
        else
        {
            if (cmd == "ld")
            {
                regs[rd] = myCache->read(adr, 8);
            }
            else if (cmd == "lw")
            {
                regs[rd] = myCache->read(adr, 4);
                if (regs[rd] & (1 << 31))
                {
                    regs[rd] = regs[rd] | 0xFFFFFFFF00000000;
                }
            }
            else if (cmd == "lh")
            {
                regs[rd] = myCache->read(adr, 2);
                if (regs[rd] & (1 << 15))
                {
                    regs[rd] = regs[rd] | 0xFFFFFFFFFFFF0000;
                }
            }
            else if (cmd == "lb")
            {
                regs[rd] = myCache->read(adr, 1);
                if (regs[rd] & (1 << 7))
                {
                    regs[rd] = regs[rd] | 0xFFFFFFFFFFFFFF00;
                }
            }
            else if (cmd == "lwu")
            {
                regs[rd] = myCache->read(adr, 4);
            }
            else if (cmd == "lhu")
            {
                regs[rd] = myCache->read(adr, 2);
            }
            else if (cmd == "lbu")
            {
                regs[rd] = myCache->read(adr, 1);
            }
        }
        cout << "Executed: " << instruction << "; PC = " << int_to_hex(PC * 4) << "\n";
        PC++;
        call_stack.top().second = PC;
    }

    else if (opMap[cmd] == opMap["sd"])
    {
        if (args.size() != 3)
        {
            cerr << "Error on line " << PC << ": Instruction " << cmd << " [rs2] [imm(12)] [rs1] expects 3 arguments but got " << args.size() << "\n";
            return;
        }

        checkReg(args[0]);
        checkReg(args[2]);

        int rs2 = regMap[args[0]];
        if (!processImm(args[1], 12, PC, false).second)
            return;
        int offset = processImm(args[1], 12, PC, false).first;
        int rs1 = regMap[args[2]];
        int adr = regs[rs1] + offset;

        if (cmd == "sd")
        {
            myCache->write(adr, regs[rs2], 8);
        }
        else if (cmd == "sw")
        {
            myCache->write(adr, regs[rs2], 4);
        }
        else if (cmd == "sh")
        {
            myCache->write(adr, regs[rs2], 2);
        }
        else if (cmd == "sb")
        {
            myCache->write(adr, regs[rs2], 1);
        }
        cout << "Executed: " << instruction << "; PC = " << int_to_hex(PC * 4) << "\n";
        PC++;
        call_stack.top().second = PC;
    }

    else if (cmd == "jal")
    {
        if (args.size() != 2)
        {
            cerr << "Error on line " << PC + 1 << ": Instruction " << cmd << " [rd] [label] expects 2 arguments but got " << args.size() << "\n";
            return;
        }
        checkReg(args[0]);
        int rd = regMap[args[0]];
        string label = args[1];

        if (lMap[label] == 0)
        {
            cerr << "Error on line " << PC + 1 << ": Unknown label '" << label << "'\n";
            return;
        }
        if (!processImm(to_string(lMap[label] / 4 - 1), 20, PC, false).second)
            return;
        int imm = processImm(to_string(lMap[label] / 4 - 1), 12, PC, false).first;
        regs[rd] = (PC + 1) * 4;
        cout << "Executed: " << instruction << "; PC = " << int_to_hex(PC * 4) << "\n";
        call_stack.top().second = PC + 1;
        PC = imm;
        call_stack.push({label, PC});
    }

    else if (cmd == "lui")
    {
        checkReg(args[0]);
        int rd = regMap[args[0]];
        if (!processImm(args[1], 20, PC, false).second)
            return;
        int imm = processImm(args[1], 20, PC, false).first;
        regs[rd] = imm;
        cout << "Executed: " << instruction << "; PC = " << int_to_hex(PC * 4) << "\n";
        PC++;
        call_stack.top().second = PC;
    }

    if (opMap[cmd] == opMap["beq"])
    {
        if (args.size() != 3)
        {
            cerr << "Error on line " << PC << ": Instruction " << cmd << " [rs1] [rs2] [label] expects 3 arguments but got " << args.size() << "\n";
            return;
        }
        checkReg(args[0]);
        checkReg(args[1]);

        int rs1 = regMap[args[0]];
        int rs2 = regMap[args[1]];
        string label = args[2];

        if (lMap[label] == 0)
        {
            cerr << "Error on line " << PC + 1 << ": Unknown label '" << label << "'\n";
            return;
        }
        if (!processImm(to_string(lMap[label] / 4 - 1), 12, PC, false).second)
            return;
        int imm = processImm(to_string(lMap[label] / 4 - 1), 12, PC, false).first;
        cout << "Executed: " << instruction << "; PC = " << int_to_hex(PC * 4) << "\n";

        if (cmd == "beq")
        {
            if (regs[rs1] == regs[rs2])
                PC = imm;
            else
                PC++;
        }

        if (cmd == "bne")
        {
            if (regs[rs1] != regs[rs2])
                PC = imm;
            else
                PC++;
        }

        if (cmd == "blt")
        {
            if (regs[rs1] < regs[rs2])
                PC = imm;
            else
                PC++;
        }

        if (cmd == "bge")
        {
            if (regs[rs1] >= regs[rs2])
                PC = imm;
            else
                PC++;
        }

        if (cmd == "bltu")
        {
            if ((unsigned long long)regs[rs1] < (unsigned long long)regs[rs2])
                PC = imm;
            else
                PC++;
        }

        if (cmd == "bgeu")
        {
            if ((unsigned long long)regs[rs1] >= (unsigned long long)regs[rs2])
                PC = imm;
            else
                PC++;
        }
        call_stack.top().second = PC;
    }
    regs[0] = 0;
    if (PC >= lines.size())
    {
        while (!call_stack.empty())
        {
            call_stack.pop();
        }
    }
}

int main()
{
    srand(time(0));
    string command;
    while (true)
    {
        cin >> command;

        if (command == "load")
        {
            if (cacheenable)
            {

                for (int i = 0; i < myCache->size / (myCache->block * myCache->assoc); i++)
                {
                    for (int j = 0; j < myCache->assoc; j++)
                    {
                        myCache->addrs[i][j] = -1;
                        myCache->durty[i][j] = 0;
                        myCache->timestamps[i][j] = 0;
                    }
                }
                myCache->hits = 0;
                myCache->miss = 0;
                for (int i = 0; i < myCache->size / (myCache->block * myCache->assoc); i++)
                {
                    while (!myCache->fifo[i].empty())
                    {
                        myCache->fifo[i].pop();
                    }
                }
            }
            for (int i = 0; i < 32; i++)
                regs[i] = 0;
            for (int i = 0; i < mem_size; i++)
                mem[i] = 0;
            lines.clear();
            lMap.clear();
            breakpoints.clear();
            PC = 0;
            call_stack = stack<pair<string, int>>({{"main", 0}});

            string input_file;
            cin >> input_file;
            ifstream inp(input_file);
            if (!inp.is_open())
            {
                cerr << "Error: Could not open input file '" << input_file << endl
                     << endl;
                continue;
            }
            execname = input_file;

            string line;
            int lineNum = 1, instrNum = 1, dataType = -1;
            bool data = false;
            unsigned long long baseAddress = 0x10000;

            while (getline(inp, line))
            {
                line = removespace(line);

                int commentPos = line.find(';');
                if (commentPos != string::npos)
                {
                    line = line.substr(0, commentPos);
                }

                if (line.empty())
                {
                    lineNum++;
                    continue;
                }

                if (line == ".data")
                {
                    data = true;
                    lMap.clear();
                    lines.clear();
                    instrNum = 1;
                    lineNum = 1;
                    continue;
                }

                if (data)
                {
                    if (line == ".text")
                    {
                        data = false;
                        continue;
                    }

                    if (line.find(".byte") == 0)
                    {
                        dataType = 0;
                        line = line.substr(5);
                    }
                    else if (line.find(".half") == 0)
                    {
                        dataType = 1;
                        line = line.substr(5);
                    }
                    else if (line.find(".word") == 0)
                    {
                        dataType = 2;
                        line = line.substr(5);
                    }
                    else if (line.find(".dword") == 0)
                    {
                        dataType = 3;
                        line = line.substr(6);
                    }

                    if (dataType == -1)
                    {
                        cerr << "Error on line " << lineNum << ": Invalid data type\n";
                        break;
                    }

                    if (dataType == 0)
                    {
                        vector<string> data = parse(line);
                        for (int i = 0; i < data.size(); i++)
                        {
                            if (!processImm(data[i], 8, lineNum, false).second)
                                break;
                            int val = processImm(data[i], 8, lineNum, false).first;
                            mem[baseAddress] = val;
                            baseAddress++;
                        }
                        lineNum++;
                    }

                    if (dataType == 1)
                    {
                        vector<string> data = parse(line);
                        for (int i = 0; i < data.size(); i++)
                        {
                            if (!processImm(data[i], 16, lineNum, false).second)
                                break;
                            int val = processImm(data[i], 16, lineNum, false).first;
                            mem[baseAddress] = val & 0xFF;
                            mem[baseAddress + 1] = (val >> 8) & 0xFF;
                            baseAddress += 2;
                        }
                        lineNum++;
                    }

                    if (dataType == 2)
                    {
                        vector<string> data = parse(line);
                        for (int i = 0; i < data.size(); i++)
                        {
                            if (!processImm(data[i], 32, lineNum, false).second)
                                break;
                            int val = processImm(data[i], 32, lineNum, false).first;
                            mem[baseAddress] = val & 0xFF;
                            mem[baseAddress + 1] = (val >> 8) & 0xFF;
                            mem[baseAddress + 2] = (val >> 16) & 0xFF;
                            mem[baseAddress + 3] = (val >> 24) & 0xFF;
                            baseAddress += 4;
                        }
                        lineNum++;
                    }

                    if (dataType == 3)
                    {
                        vector<string> data = parse(line);
                        for (int i = 0; i < data.size(); i++)
                        {
                            long int val;
                            if (dword_to_int(data[i], lineNum).second)
                                val = dword_to_int(data[i], lineNum).first;
                            else
                                break;
                            mem[baseAddress] = val & 0xFF;
                            mem[baseAddress + 1] = (long long)(val >> 8) & 0xFF;
                            mem[baseAddress + 2] = (long long)(val >> 16) & 0xFF;
                            mem[baseAddress + 3] = (long long)(val >> 24) & 0xFF;
                            mem[baseAddress + 4] = (long long)(val >> 32) & 0xFF;
                            mem[baseAddress + 5] = (long long)(val >> 40) & 0xFF;
                            mem[baseAddress + 6] = (long long)(val >> 48) & 0xFF;
                            mem[baseAddress + 7] = (long long)(val >> 56) & 0xFF;
                            baseAddress += 8;
                        }
                        lineNum++;
                    }
                }

                else
                {
                    int col = line.find(':');
                    if (col != string::npos)
                    {
                        string label = line.substr(0, col);
                        if (lMap.find(label) != lMap.end())
                        {
                            lines.clear();
                            lMap.clear();
                            cerr << "Error on line " << lineNum << ": Multiple definitions of label '" << label << "'" << endl
                                 << endl;
                            break;
                        }
                        lMap[label] = 4 * instrNum;
                        line = line.substr(col + 2);
                    }

                    if (!line.empty())
                        instrNum++;

                    lines.push_back(line);
                    lineNum++;
                }
            }
            cout << endl;
        }

        else if (command == "reload")
        {
            breakpoints.clear();
            PC = 0;
            call_stack = stack<pair<string, int>>({{"main", 0}});
            for (int i = 0; i < 32; i++)
                regs[i] = 0;
            for (int i = 0; i < mem_size; i++)
                mem[i] = 0;
        }

        else if (command == "run")
        {
            while (PC < lines.size())
            {
                if (find(breakpoints.begin(), breakpoints.end(), PC + 1) != breakpoints.end())
                {
                    cout << "Execution stopped at breakpoint\n";
                    break;
                }
                string instruction = lines[PC];
                execute(instruction);
            }
            if (cacheenable)
            {
                int accesses = myCache->hits + myCache->miss;
                double hitRate = (accesses > 0) ? static_cast<double>(myCache->hits) / accesses : 0.0;
                cout << "D-cache statistics: Accesses=" << accesses << ", Hit=" << myCache->hits << ", Miss=" << myCache->miss << ", Hit Rate=" << fixed << setprecision(2) << hitRate << "\n";
            }
            cout << endl;
        }

        else if (command == "regs")
        {
            for (int i = 0; i < 32; i++)
            {
                cout << "x" << i << ": ";
                cout << int_to_hex(regs[i], 64) << endl;
            }
            cout << endl;
        }

        else if (command == "mem")
        {
            unsigned int adr;
            int count;
            cin >> hex >> adr >> count;

            for (int i = 0; i < count; i++)
            {
                if (adr + i < mem_size)
                {
                    cout << "Memory[" << int_to_hex(adr + i, 20) << "] = " << int_to_hex(mem[adr + i]) << endl;
                }
                else
                {
                    cout << adr + i << ": Out of bounds" << endl;
                }
            }
            cout << endl;
        }

        else if (command == "step")
        {
            if (PC >= lines.size())
            {
                cout << "Nothing to step\n\n";
                if (cacheenable)
                {
                    int accesses = myCache->hits + myCache->miss;
                    double hitRate = (accesses > 0) ? static_cast<double>(myCache->hits) / accesses : 0.0;
                    cout << "D-cache statistics: Accesses=" << accesses << ", Hit=" << myCache->hits << ", Miss=" << myCache->miss << ", Hit Rate=" << fixed << setprecision(2) << hitRate << "\n";
                }
                continue;
            }
            string instruction = lines[PC];
            execute(instruction);
            cout << endl;
        }

        else if (command == "show-stack")
        {
            if (call_stack.empty())
            {
                cout << "Empty Call Stack: Execution complete\n\n";
            }
            cout << "Call Stack:\n";
            stack<pair<string, int>> dum_stack = call_stack;
            stack<pair<string, int>> rev_stack;

            while (!dum_stack.empty())
            {
                rev_stack.push(dum_stack.top());
                dum_stack.pop();
            }

            while (!rev_stack.empty())
            {
                cout << rev_stack.top().first << ":" << rev_stack.top().second << "\n";
                rev_stack.pop();
            }
            cout << endl;
        }

        else if (command == "break")
        {
            int lineNum;
            cin >> lineNum;
            breakpoints.push_back(lineNum);
            cout << "Breakpoint set at line " << lineNum << "\n\n";
        }

        else if (command == "del")
        {
            string type;
            cin >> type;
            if (type == "break")
            {
                int lineNum;
                cin >> lineNum;
                int i;
                for (i = 0; i < breakpoints.size(); i++)
                {
                    if (breakpoints[i] == lineNum)
                    {
                        breakpoints.erase(breakpoints.begin() + i);
                        cout << "Breakpoint deleted at line " << lineNum << "\n\n";
                        break;
                    }
                }
                if (i == breakpoints.size())
                {
                    cout << "No breakpoint set at line " << lineNum << "\n\n";
                }
            }
        }

        else if (command == "exit")
        {
            cout << "Exited the simulator. Thank you!\n";
            return 0;
        }

        else if (command == "cache_sim")
        {
            string subcommand;
            cin >> subcommand;

            if (subcommand == "enable")
            {
                string config_file;
                cin >> config_file;
                ifstream inp(config_file);

                if (!inp.is_open())
                {
                    cerr << "Error: Could not open config file " << config_file << "\n";
                    break;
                }

                int size, block, assoc;
                string repl, write;

                inp >> size >> block >> assoc >> repl >> write;

                if (assoc == 0)
                {
                    assoc = size / block;
                }

                int replacem;
                if (repl == "LRU")
                    replacem = 0;
                else if (repl == "FIFO")
                    replacem = 1;
                else
                    replacem = 2;
                int writem = (write == "WT") ? 0 : 1;

                delete myCache;
                myCache = new Cache(size, block, assoc, replacem, writem);
                cacheenable = 1;
            }

            else if (subcommand == "disable")
            {
                cacheenable = 0;
                if (myCache)
                {
                    for (int i = 0; i < myCache->size / (myCache->block * myCache->assoc); i++)
                    {
                        delete[] myCache->data[i];
                        delete[] myCache->addrs[i];
                        delete[] myCache->durty[i];
                    }
                    delete[] myCache->data;
                    delete[] myCache->addrs;
                    delete[] myCache->durty;
                    delete myCache;
                    myCache = nullptr;
                }
            }

            else if (subcommand == "status")
            {
                if (cacheenable)
                {
                    cout << "Cache simulation is enabled.\n";
                    cout << "Cache size: " << myCache->size << " bytes\n";
                    cout << "Block size: " << myCache->block << " bytes\n";
                    cout << "Associativity: " << myCache->assoc << "\n";
                    if (myCache->repl == 0)
                    {
                        cout << "Replacement policy: LRU\n";
                    }
                    else if (myCache->repl == 1)
                    {
                        cout << "Replacement policy: FIFO\n";
                    }
                    else
                    {
                        cout << "Replacement policy: RAND\n";
                    }
                    cout << "Write policy: " << (myCache->writep == 0 ? "WT" : "WB") << "\n";
                    cout << "Cache hits: " << myCache->hits << "\n";
                    cout << "Cache misses: " << myCache->miss << "\n";
                }
                else
                {
                    cout << "Cache simulation is disabled.\n";
                }
                cout << endl;
            }

            else if (subcommand == "invalidate")
            {
                if (cacheenable)
                {
                    int indexSize = (int)log2(myCache->size / (myCache->block * myCache->assoc));
                    int offset = (int)log2(myCache->block);
                    for (int i = 0; i < myCache->size / (myCache->block * myCache->assoc); i++)
                    {
                        for (int j = 0; j < myCache->assoc; j++)
                        {
                            if (myCache->durty[i][j] == 1)
                            {
                                int addr = myCache->addrs[i][j] << (offset + indexSize);
                                addr |= i << offset;
                                for (int k = 0; k < myCache->block; k++)
                                {
                                    mem[addr + k] = myCache->data[i][j * myCache->block + k];
                                }
                            }
                            myCache->addrs[i][j] = -1;
                            myCache->durty[i][j] = 0;
                        }
                    }
                }
                else
                {
                    cout << "Cache simulation is disabled.\n";
                }
                cout << endl;
            }

            else if (subcommand == "dump")
            {

                string filename;
                cin >> filename;
                ofstream outfile(filename);

                if (!outfile.is_open())
                {
                    cerr << "Error: Could not open file " << filename << " for writing.\n";
                    continue;
                }
                for (int i = 0; i < myCache->size / (myCache->block * myCache->assoc); i++)
                {
                    for (int j = 0; j < myCache->assoc; j++)
                    {
                        if (myCache->addrs[i][j] != -1)
                        {
                            outfile << "Set: 0x" << hex << i << ", Tag: 0x" << hex << myCache->addrs[i][j] << ", " << (myCache->durty[i][j] ? "Dirty" : "Clean") << "\n";
                        }
                    }
                }
                outfile.close();
            }

            else if (subcommand == "stats")
            {
                if (cacheenable)
                {
                    int accesses = myCache->hits + myCache->miss;
                    double hitRate = (accesses > 0) ? static_cast<double>(myCache->hits) / accesses : 0.0;
                    cout << "D-cache statistics: Accesses=" << accesses << ", Hit=" << myCache->hits << ", Miss=" << myCache->miss << ", Hit Rate=" << fixed << setprecision(2) << hitRate << "\n";
                }
                else
                {
                    cout << "Cache simulation is disabled.\n";
                }
                cout << endl;
            }
        }

        else
        {
            cout << "Unknown command: " << command << ". Please enter a valid command\n";
        }
    }
}
