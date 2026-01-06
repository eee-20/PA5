#include "cgen.h"
#include "cool-tree.h"
#include "cool-tree.handcode.h"
#include "stringtab.h"
#include "emit.h"
#include <vector>
#include <map>
#include <algorithm>

using namespace std;

// 全局变量：标签计数器
int labelnum = 0;
// GC开关（0关闭，1开启）
int cgen_Memmgr = 0;

// 寄存器别名定义
#define ACC "$a0"
#define SELF "$s0"
#define FP "$fp"
#define SP "$sp"
#define RA "$ra"
#define T1 "$t1"
#define T2 "$t2"
#define T3 "$t3"
#define ZERO "$zero"

// 常量后缀定义
#define PROTOBJ_SUFFIX "_protObj"
#define DISPTAB_SUFFIX "_dispTab"
#define CLASSINIT_SUFFIX "_init"
#define STRCONST_PREFIX "str_const"
#define INTCONST_PREFIX "int_const"
#define BOOLCONST_PREFIX "bool_const"

// 默认对象字段数（tag、size、dispatch table）
#define DEFAULT_OBJFIELDS 3
#define STRING_SLOTS 1
#define INT_SLOTS 1
#define BOOL_SLOTS 1

// 全局类表指针
CgenClassTable* codegen_classtable;

// Environment类实现
class Environment {
private:
    struct Scope {
        map<Symbol, int> vars;
        int var_count = 0;
    };
    vector<Scope> scopes;
    map<Symbol, int> params;
    int param_count = 0;
public:
    CgenNode* m_class_node;

    int LookUpVar(Symbol sym) {
        for (auto it = scopes.rbegin(); it != scopes.rend(); ++it) {
            if (it->vars.count(sym)) return it->vars[sym];
        }
        return -1;
    }

    int LookUpParam(Symbol sym) {
        return params.count(sym) ? params[sym] : -1;
    }

    int LookUpAttrib(Symbol sym) {
        if (!m_class_node) return -1;
        auto& idx_tab = m_class_node->GetAttribIdxTab();
        return idx_tab.count(sym) ? idx_tab[sym] : -1;
    }

    void EnterScope() { scopes.emplace_back(); }
    void ExitScope() { if (!scopes.empty()) scopes.pop_back(); }
    void AddVar(Symbol sym) { scopes.back().vars[sym] = scopes.back().var_count++; }
    void AddParam(Symbol sym) { params[sym] = param_count++; }
    void AddObstacle() {}  // GC相关占位
};

// CgenNode类实现
class CgenNode {
private:
    Symbol name;
    Symbol parent;
    CgenNode* parentnd;
    Features features;
    int class_tag;
    vector<CgenNode*> inheritance;
    vector<attr_class*> m_full_attribs;
    vector<method_class*> m_full_methods;
    map<Symbol, int> m_attrib_idx_tab;
    map<Symbol, int> m_dispatch_idx_tab;
    map<Symbol, Symbol> m_dispatch_class_tab;

public:
    CgenNode(Class_ c) {
        name = c->get_name();
        parent = c->get_parent();
        features = c->get_features();
        parentnd = nullptr;
        class_tag = -1;
    }

    Symbol get_name() { return name; }
    Symbol get_parent() { return parent; }
    CgenNode* get_parentnd() { return parentnd; }
    void set_parentnd(CgenNode* p) { parentnd = p; }
    int get_tag() { return class_tag; }
    void set_tag(int t) { class_tag = t; }

    // 获取继承链
    vector<CgenNode*> GetInheritance() {
        if (inheritance.empty()) {
            CgenNode* curr = this;
            while (curr) {
                inheritance.push_back(curr);
                curr = curr->parentnd;
            }
            reverse(inheritance.begin(), inheritance.end());
        }
        return inheritance;
    }

    // 获取完整属性列表（含继承）
    vector<attr_class*> GetFullAttribs() {
        if (m_full_attribs.empty()) {
            vector<CgenNode*> chain = GetInheritance();
            for (auto node : chain) {
                Features fs = node->features;
                for (int i = fs->first(); fs->more(i); i = fs->next(i)) {
                    Feature f = fs->nth(i);
                    if (f->is_attr()) {
                        m_full_attribs.push_back(static_cast<attr_class*>(f));
                    }
                }
            }
            // 构建属性索引表
            for (int i = 0; i < m_full_attribs.size(); ++i) {
                m_attrib_idx_tab[m_full_attribs[i]->get_name()] = i;
            }
        }
        return m_full_attribs;
    }

    // 获取当前类属性（不含继承）
    vector<attr_class*> GetAttribs() {
        vector<attr_class*> res;
        for (int i = features->first(); features->more(i); i = features->next(i)) {
            Feature f = features->nth(i);
            if (f->is_attr()) {
                res.push_back(static_cast<attr_class*>(f));
            }
        }
        return res;
    }

    // 获取完整方法列表（含继承和重写）
    vector<method_class*> GetFullMethods() {
        if (m_full_methods.empty()) {
            vector<CgenNode*> chain = GetInheritance();
            for (auto node : chain) {
                Features fs = node->features;
                for (int i = fs->first(); fs->more(i); i = fs->next(i)) {
                    Feature f = fs->nth(i);
                    if (f->is_method()) {
                        method_class* m = static_cast<method_class*>(f);
                        Symbol mname = m->get_name();
                        if (m_dispatch_idx_tab.count(mname) == 0) {
                            m_dispatch_idx_tab[mname] = m_full_methods.size();
                            m_dispatch_class_tab[mname] = node->get_name();
                            m_full_methods.push_back(m);
                        } else {
                            // 方法重写：替换为子类方法
                            int idx = m_dispatch_idx_tab[mname];
                            m_full_methods[idx] = m;
                            m_dispatch_class_tab[mname] = node->get_name();
                        }
                    }
                }
            }
        }
        return m_full_methods;
    }

    // 获取当前类方法（不含继承）
    vector<method_class*> GetMethods() {
        vector<method_class*> res;
        for (int i = features->first(); features->more(i); i = features->next(i)) {
            Feature f = features->nth(i);
            if (f->is_method()) {
                res.push_back(static_cast<method_class*>(f));
            }
        }
        return res;
    }

    map<Symbol, int> GetAttribIdxTab() { return m_attrib_idx_tab; }
    map<Symbol, int> GetDispatchIdxTab() { return m_dispatch_idx_tab; }
    map<Symbol, Symbol> GetDispatchClassTab() { return m_dispatch_class_tab; }

    // 生成原型对象代码
    void code_protObj(ostream& s) {
        vector<attr_class*> attribs = GetFullAttribs();
        s << "\t.word -1" << endl;  // GC标记
        s << get_name()->get_string() << PROTOBJ_SUFFIX << ":" << endl;
        s << "\t.word " << class_tag << "\t# class tag" << endl;
        s << "\t.word " << (DEFAULT_OBJFIELDS + attribs.size()) << "\t# size" << endl;
        s << "\t.word " << get_name()->get_string() << DISPTAB_SUFFIX << endl;

        // 初始化属性默认值
        for (auto attr : attribs) {
            Symbol type = attr->get_type_decl();
            if (type == int_class) {
                s << "\t.word " << INTCONST_PREFIX << "0" << "\t# int(0)" << endl;
            } else if (type == bool_class) {
                s << "\t.word " << BOOLCONST_PREFIX << "0" << "\t# bool(false)" << endl;
            } else if (type == string_class) {
                s << "\t.word " << STRCONST_PREFIX << "0" << "\t# str()" << endl;
            } else {
                s << "\t.word 0\t# void" << endl;
            }
        }
    }

    // 生成初始化方法代码
    void code_init(ostream& s) {
        s << get_name()->get_string() << CLASSINIT_SUFFIX << ":" << endl;
        // 保存寄存器
        emit_addiu(SP, SP, -12, s);
        emit_store(FP, 3, SP, s);
        emit_store(SELF, 2, SP, s);
        emit_store(RA, 1, SP, s);
        emit_addiu(FP, SP, 4, s);
        emit_move(SELF, ACC, s);

        // 调用父类初始化
        if (parentnd && parentnd->get_name() != no_class) {
            s << "\t# Call parent init" << endl;
            emit_jal((parentnd->get_name()->get_string() + CLASSINIT_SUFFIX).c_str(), s);
        }

        // 初始化当前类属性
        vector<attr_class*> attribs = GetAttribs();
        map<Symbol, int> idx_tab = GetAttribIdxTab();
        for (auto attr : attribs) {
            Symbol aname = attr->get_name();
            int idx = idx_tab[aname];
            Expression init = attr->get_init();
            Environment env;
            env.m_class_node = this;

            if (init->is_no_expr()) {
                // 使用默认值
                Symbol type = attr->get_type_decl();
                if (type == string_class) {
                    emit_load_string(ACC, stringtable.lookup_string(""), s);
                } else if (type == int_class) {
                    emit_load_int(ACC, inttable.lookup_string("0"), s);
                } else if (type == bool_class) {
                    emit_load_bool(ACC, BoolConst(0), s);
                } else {
                    emit_move(ACC, ZERO, s);
                }
            } else {
                // 计算初始化表达式
                init->code(s, env);
            }
            emit_store(ACC, 3 + idx, SELF, s);
        }

        // 返回self
        emit_move(ACC, SELF, s);
        // 恢复寄存器
        emit_load(FP, 3, SP, s);
        emit_load(SELF, 2, SP, s);
        emit_load(RA, 1, SP, s);
        emit_addiu(SP, SP, 12, s);
        emit_return(s);
    }

    // 生成方法代码
    void code_methods(ostream& s) {
        vector<method_class*> methods = GetMethods();
        for (auto m : methods) {
            m->code(s, this);
        }
    }
};

// CgenClassTable类实现
class CgenClassTable {
private:
    vector<CgenNode*> m_class_nodes;
    map<Symbol, CgenNode*> m_class_map;
    map<Symbol, int> m_class_tags;
    ostream& str;

    // 安装基础类
    void install_basic_classes() {
        // 基础类（Object、IO、Int、Bool、String）已由系统提供
        // 此处仅建立节点映射
        Symbol obj_sym = intern_str("Object");
        Symbol io_sym = intern_str("IO");
        Symbol int_sym = intern_str("Int");
        Symbol bool_sym = intern_str("Bool");
        Symbol str_sym = intern_str("String");

        m_class_map[obj_sym] = new CgenNode(Class_(obj_sym, no_class, nil_Features()));
        m_class_map[io_sym] = new CgenNode(Class_(io_sym, obj_sym, nil_Features()));
        m_class_map[int_sym] = new CgenNode(Class_(int_sym, obj_sym, nil_Features()));
        m_class_map[bool_sym] = new CgenNode(Class_(bool_sym, obj_sym, nil_Features()));
        m_class_map[str_sym] = new CgenNode(Class_(str_sym, obj_sym, nil_Features()));

        // 设置父节点
        m_class_map[io_sym]->set_parentnd(m_class_map[obj_sym]);
        m_class_map[int_sym]->set_parentnd(m_class_map[obj_sym]);
        m_class_map[bool_sym]->set_parentnd(m_class_map[obj_sym]);
        m_class_map[str_sym]->set_parentnd(m_class_map[obj_sym]);
    }

    // 构建继承树
    void build_inheritance_tree() {
        for (auto node : m_class_nodes) {
            Symbol parent_sym = node->get_parent();
            if (m_class_map.count(parent_sym)) {
                node->set_parentnd(m_class_map[parent_sym]);
            } else {
                cerr << "Error: Parent class " << parent_sym->get_string() << " not found" << endl;
            }
        }

        // 分配类标签
        int tag = 0;
        for (auto node : m_class_nodes) {
            node->set_tag(tag);
            m_class_tags[node->get_name()] = tag++;
        }
    }

public:
    CgenClassTable(Classes classes, ostream& s) : str(s) {
        install_basic_classes();
        // 安装用户类
        for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
            Class_ c = classes->nth(i);
            Symbol cname = c->get_name();
            CgenNode* node = new CgenNode(c);
            m_class_nodes.push_back(node);
            m_class_map[cname] = node;
        }
        build_inheritance_tree();
        codegen_classtable = this;
    }

    vector<CgenNode*> GetClassNodes() { return m_class_nodes; }
    CgenNode* GetClassNode(Symbol sym) { return m_class_map[sym]; }
    map<Symbol, int> GetClassTags() { return m_class_tags; }

    // 生成全局数据段
    void code_global_data() {
        str << ".data" << endl;
        str << ".align 2" << endl;
        code_constants();
        code_class_nameTab();
        code_class_objTab();
        code_dispatchTabs();
        code_protObjs();
    }

    // 生成常量
    void code_constants() {
        // 添加基础常量
        stringtable.add_string("");
        inttable.add_string("0");

        // 生成字符串常量
        str << "# String constants" << endl;
        stringtable.code_string_table(str, m_class_tags[string_class]);

        // 生成整数常量
        str << "# Integer constants" << endl;
        inttable.code_string_table(str, m_class_tags[int_class]);

        // 生成布尔常量
        str << "# Boolean constants" << endl;
        code_bools(m_class_tags[bool_class]);
    }

    // 生成布尔常量
    void code_bools(int bool_tag) {
        // false
        str << "\t.word -1" << endl;
        str << BOOLCONST_PREFIX << "0:" << endl;
        str << "\t.word " << bool_tag << endl;
        str << "\t.word " << (DEFAULT_OBJFIELDS + BOOL_SLOTS) << endl;
        str << "\t.word Bool" << DISPTAB_SUFFIX << endl;
        str << "\t.word 0" << endl;

        // true
        str << "\t.word -1" << endl;
        str << BOOLCONST_PREFIX << "1:" << endl;
        str << "\t.word " << bool_tag << endl;
        str << "\t.word " << (DEFAULT_OBJFIELDS + BOOL_SLOTS) << endl;
        str << "\t.word Bool" << DISPTAB_SUFFIX << endl;
        str << "\t.word 1" << endl;
    }

    // 生成类名表
    void code_class_nameTab() {
        str << "# Class name table" << endl;
        str << "class_nameTab:" << endl;
        for (auto node : m_class_nodes) {
            Symbol cname = node->get_name();
            StringEntry* se = stringtable.lookup_string(cname->get_string());
            str << "\t.word ";
            se->code_ref(str);
            str << endl;
        }
    }

    // 生成对象表
    void code_class_objTab() {
        str << "# Class object table" << endl;
        str << "class_objTab:" << endl;
        for (auto node : m_class_nodes) {
            Symbol cname = node->get_name();
            // 原型对象地址
            str << "\t.word " << cname->get_string() << PROTOBJ_SUFFIX << endl;
            // 初始化方法地址
            str << "\t.word " << cname->get_string() << CLASSINIT_SUFFIX << endl;
        }
    }

    // 生成分发表
    void code_dispatchTabs() {
        str << "# Dispatch tables" << endl;
        for (auto node : m_class_nodes) {
            Symbol cname = node->get_name();
            str << cname->get_string() << DISPTAB_SUFFIX << ":" << endl;
            vector<method_class*> methods = node->GetFullMethods();
            for (auto m : methods) {
                str << "\t.word ";
                Symbol mname = m->get_name();
                Symbol def_class = node->GetDispatchClassTab()[mname];
                str << def_class->get_string() << "_" << mname->get_string();
                str << endl;
            }
        }
    }

    // 生成原型对象
    void code_protObjs() {
        str << "# Prototype objects" << endl;
        for (auto node : m_class_nodes) {
            node->code_protObj(str);
        }
    }

    // 生成全局文本段
    void code_global_text() {
        str << ".text" << endl;
        str << ".align 2" << endl;
        code_class_inits();
        code_class_methods();
    }

    // 生成初始化方法
    void code_class_inits() {
        str << "# Class init methods" << endl;
        for (auto node : m_class_nodes) {
            node->code_init(str);
        }
    }

    // 生成类方法
    void code_class_methods() {
        str << "# Class methods" << endl;
        for (auto node : m_class_nodes) {
            node->code_methods(str);
        }
    }

    // 生成完整代码
    void code() {
        code_global_data();
        code_global_text();
    }
};

// 表达式节点code()方法实现
// 整数常量
void int_const_class::code(ostream& s, Environment env) {
    emit_load_int(ACC, inttable.lookup_string(token->get_string()), s);
}

// 字符串常量
void string_const_class::code(ostream& s, Environment env) {
    emit_load_string(ACC, stringtable.lookup_string(token->get_string()), s);
}

// 布尔常量
void bool_const_class::code(ostream& s, Environment env) {
    emit_load_bool(ACC, BoolConst(val), s);
}

// 对象引用
void object_class::code(ostream& s, Environment env) {
    int idx;
    if ((idx = env.LookUpVar(name)) != -1) {
        emit_load(ACC, idx + 1, SP, s);
    } else if ((idx = env.LookUpParam(name)) != -1) {
        emit_load(ACC, idx + 3, FP, s);
    } else if ((idx = env.LookUpAttrib(name)) != -1) {
        emit_load(ACC, idx + 3, SELF, s);
    } else if (name == self) {
        emit_move(ACC, SELF, s);
    } else {
        yyerror(("Undefined variable: " + name->get_string()).c_str());
    }
}

// 赋值表达式
void assign_class::code(ostream& s, Environment env) {
    expr->code(s, env);
    int idx;
    if ((idx = env.LookUpVar(name)) != -1) {
        emit_store(ACC, idx + 1, SP, s);
        if (cgen_Memmgr == 1) {
            emit_addiu("$a1", SP, 4 * (idx + 1), s);
            emit_jal("_GenGC_Assign", s);
        }
    } else if ((idx = env.LookUpParam(name)) != -1) {
        emit_store(ACC, idx + 3, FP, s);
        if (cgen_Memmgr == 1) {
            emit_addiu("$a1", FP, 4 * (idx + 3), s);
            emit_jal("_GenGC_Assign", s);
        }
    } else if ((idx = env.LookUpAttrib(name)) != -1) {
        emit_store(ACC, idx + 3, SELF, s);
        if (cgen_Memmgr == 1) {
            emit_addiu("$a1", SELF, 4 * (idx + 3), s);
            emit_jal("_GenGC_Assign", s);
        }
    } else {
        yyerror(("Assignment to undefined variable: " + name->get_string()).c_str());
    }
}

// 加法表达式
void plus_class::code(ostream& s, Environment env) {
    e1->code(s, env);
    emit_push(ACC, s);
    env.AddObstacle();

    e2->code(s, env);
    emit_jal("Object.copy", s);

    emit_addiu(SP, SP, 4, s);
    emit_load(T1, 0, SP, s);
    emit_move(T2, ACC, s);

    emit_load(T1, 3, T1, s);
    emit_load(T2, 3, T2, s);

    emit_add(T3, T1, T2, s);
    emit_store(T3, 3, ACC, s);
}

// 条件表达式
void cond_class::code(ostream& s, Environment env) {
    pred->code(s, env);
    emit_fetch_int(T1, ACC, s);

    int label_false = labelnum++;
    int label_finish = labelnum++;

    emit_beq(T1, ZERO, label_false, s);
    then_exp->code(s, env);
    emit_branch(label_finish, s);

    emit_label_def(label_false, s);
    else_exp->code(s, env);

    emit_label_def(label_finish, s);
}

// 循环表达式
void loop_class::code(ostream& s, Environment env) {
    int start = labelnum++;
    int finish = labelnum++;

    emit_label_def(start, s);
    pred->code(s, env);
    emit_fetch_int(T1, ACC, s);
    emit_beq(T1, ZERO, finish, s);

    body->code(s, env);
    emit_branch(start, s);

    emit_label_def(finish, s);
    emit_move(ACC, ZERO, s);
}

// let表达式
void let_class::code(ostream& s, Environment env) {
    init->code(s, env);
    if (init->is_no_expr()) {
        if (type_decl == string_class) {
            emit_load_string(ACC, stringtable.lookup_string(""), s);
        } else if (type_decl == int_class) {
            emit_load_int(ACC, inttable.lookup_string("0"), s);
        } else if (type_decl == bool_class) {
            emit_load_bool(ACC, BoolConst(0), s);
        } else {
            emit_move(ACC, ZERO, s);
        }
    }

    emit_push(ACC, s);
    env.EnterScope();
    env.AddVar(identifier);

    body->code(s, env);

    emit_addiu(SP, SP, 4, s);
    env.ExitScope();
}

// 方法调用
vector<Expression> dispatch_class::GetActuals() {
    vector<Expression> ret;
    for (int i = actual->first(); actual->more(i); i = actual->next(i)) {
        ret.push_back(actual->nth(i));
    }
    return ret;
}

void dispatch_class::code(ostream& s, Environment env) {
    vector<Expression> actuals = GetActuals();
    for (auto it = actuals.rbegin(); it != actuals.rend(); ++it) {
        (*it)->code(s, env);
        emit_push(ACC, s);
        env.AddObstacle();
    }

    expr->code(s, env);

    emit_bne(ACC, ZERO, labelnum, s);
    emit_load_address(ACC, STRCONST_PREFIX "0", s);
    emit_load_imm(T1, 1, s);
    emit_jal("_dispatch_abort", s);
    emit_label_def(labelnum, s);
    ++labelnum;

    Symbol class_name = env.m_class_node->get_name();
    if (expr->get_type() != self_type) {
        class_name = expr->get_type();
    }
    CgenNode* class_node = codegen_classtable->GetClassNode(class_name);

    emit_load(T1, 2, ACC, s);
    int idx = class_node->GetDispatchIdxTab()[name];
    emit_load(T1, idx, T1, s);

    emit_jalr(T1, s);

    // 清理参数栈
    emit_addiu(SP, SP, actuals.size() * 4, s);
}

// new表达式
void new__class::code(ostream& s, Environment env) {
    if (type_name == self_type) {
        emit_load_address(T1, "class_objTab", s);
        emit_load(T2, 0, SELF, s);
        emit_sll(T2, T2, 3, s);
        emit_addu(T1, T1, T2, s);
        emit_push(T1, s);
        emit_load(ACC, 0, T1, s);
        emit_jal("Object.copy", s);
        emit_load(T1, 1, SP, s);
        emit_addiu(SP, SP, 4, s);
        emit_load(T1, 1, T1, s);
        emit_jalr(T1, s);
    } else {
        string protobj = type_name->get_string() + PROTOBJ_SUFFIX;
        emit_load_address(ACC, protobj.c_str(), s);
        emit_jal("Object.copy", s);
        string init = type_name->get_string() + CLASSINIT_SUFFIX;
        emit_jal(init.c_str(), s);
    }
}

// 块表达式
void block_class::code(ostream& s, Environment env) {
    for (int i = body->first(); body->more(i); i = body->next(i)) {
        body->nth(i)->code(s, env);
    }
}

// 方法代码生成
void method_class::code(ostream& s, CgenNode* class_node) {
    string method_name = class_node->get_name()->get_string() + "_" + name->get_string();
    s << method_name << ":" << endl;

    // 保存寄存器
    emit_addiu(SP, SP, -12, s);
    emit_store(FP, 3, SP, s);
    emit_store(SELF, 2, SP, s);
    emit_store(RA, 1, SP, s);
    emit_addiu(FP, SP, 4, s);
    emit_move(SELF, ACC, s);

    // 初始化参数环境
    Environment env;
    env.m_class_node = class_node;
    for (int i = formals->first(); formals->more(i); i = formals->next(i)) {
        env.AddParam(formals->nth(i)->get_name());
    }

    // 生成方法体代码
    expr->code(s, env);

    // 恢复寄存器
    emit_load(FP, 3, SP, s);
    emit_load(SELF, 2, SP, s);
    emit_load(RA, 1, SP, s);
    emit_addiu(SP, SP, 12, s);

    // 清理参数栈
    int arg_num = formals->len();
    emit_addiu(SP, SP, arg_num * 4, s);

    emit_return(s);
}

// 程序入口
void program_class::cgen(ostream& s) {
    CgenClassTable classtable(classes, s);
    classtable.code();
}

// 辅助函数：加载整数常量
void emit_load_int(char* reg, StringEntry* se, ostream& s) {
    s << "\tla " << reg << ", " << INTCONST_PREFIX << se->index() << endl;
}

// 辅助函数：加载字符串常量
void emit_load_string(char* reg, StringEntry* se, ostream& s) {
    s << "\tla " << reg << ", " << STRCONST_PREFIX << se->index() << endl;
}

// 辅助函数：加载布尔常量
void emit_load_bool(char* reg, BoolConst bc, ostream& s) {
    s << "\tla " << reg << ", " << BOOLCONST_PREFIX << bc.val() << endl;
}

// 辅助函数：提取整数值
void emit_fetch_int(char* reg, char* obj_reg, ostream& s) {
    emit_load(reg, 3, obj_reg, s);
}
