#include <iostream>
#include <fstream>
#include <random>
#include <string>
#include <algorithm>
#include <iterator>
#include <sstream>
#include <utility>
#include <vector>
#include <map>
#include <set>
#include <unordered_set>
#include <unordered_map>
#include <ctime>
#include <cstdlib>
#include <stack>
#include <queue>
#include <dirent.h>
#include <regex>

using namespace std;

ofstream textFileTimes;
ofstream textFileSteps;
ofstream solutionFile;
ofstream proofFile;
unsigned int COUNTER = 0;
unsigned int RESTART_COUNTER = 0;
unsigned int RESTARTS = 0;
bool proof = false;

/* Namespace to define variations of algorithms that bundles names as access points */
namespace Algorithm {
    enum Version {
        DEFAULT, HEU_LIT, AUT, NO_PREP, PS
    };
    // All: Contains all variants
    static const Version All[] = {DEFAULT, AUT, HEU_LIT};
    // Contains only the default variant
    static const Version Default[] = {DEFAULT};
    static const Version NoPP[] = {NO_PREP};


    // Return a more informative string if needed.
    string getVersionName(enum Version algorithm) {
        switch (algorithm) {
            case DEFAULT:
                return "Heuristic VMTF";
            case HEU_LIT:
                return "Heuristic Literals";
            case AUT:
                return "Autartic";
            case PS:
                return "Phase Saving";
            case NO_PREP:
                return "No preprocessing";
            default:
                return "Something went wrong?!";
        }
    }
}

// Helper-function to print a vector to the console.
void printVector(const vector<int> &vector) { /* Prints a vector. */
    cout << "[ ";
    for (int j : vector) {
        cout << j << " ";
    }
    cout << "]";
}

void printVectorOfVectors(const vector<vector<int>> &vector) { /* Prints a vector of vectors. */
    for (auto &vec : vector) {
        printVector(vec);
    }
    cout << endl;
}

template<typename T>
void moveToFront(vector<T> &v, size_t index) {
    auto it = v.begin() + index;
    rotate(v.begin(), it, it + 1);
}

/** Data structure used for the VMTF heuristic */
struct EntryVMTF {
    int literal;
    int counter;
    int counter2;

    EntryVMTF(int literal, int counter, int counter2) : literal(literal), counter(counter), counter2(counter2) {}
};

/* Data structure for clauses that also stores the original clause */
struct Clause {
    vector<int> clause;
    vector<int> originalClause;
    bool conflictClause;
    bool discarded = false;

    explicit Clause(const vector<int> &clause, bool conflictClause = false) {
        this->clause = clause;
        this->originalClause = clause;
        this->conflictClause = conflictClause;
    }
};

/* Removes clauses which are satisfied by a given assignment (alpha). */
vector<Clause> removeSatisfiedClauses(const vector<Clause> &cnf, unordered_set<int> alpha) {
    vector<Clause> filteredCnf;
    for (const Clause &c : cnf) {
        bool remove = false;
        for (int v : c.clause) {
            if (alpha.find(v) != alpha.end()) {
                remove = true;
                break;
            }
        }
        if (!remove)
            filteredCnf.push_back(c);
    }
    // cout << "Done! (Clauses old: " << cnf.size() << " | Clauses new: " << filteredCnf.size() << ")." << endl;
    return filteredCnf;
}

/** Entry node for the ImplicationGraph. */
struct Node {
    int literal;
    unsigned int level;
    set<Node *> reasons;
    set<Node *> implications;
    set<Node *> origins;

    explicit Node(int literal, unsigned int level) {
        this->literal = literal;
        this->level = level;
    }

    /* Recalculates the max level base don its reasons. */
    void updateReasoning() {
        level = 0;
        for (auto edge : set<Node *>(reasons)) {
            level = max(level, edge->level);
            edge->implications.insert(this);
        }
    }

    /* Returns the children (i.e reasons/cuts) that are less than a specific level! */
    set<Node *> getChildrenUpperLimit(unsigned int maxLevelIndex) {
        if (!origins.empty())
            return origins;
        set<Node *> children;
        if (level < maxLevelIndex || reasons.empty())
            return set<Node *>({this});
        for (auto edge : reasons) {
            auto subChildren = edge->getChildrenUpperLimit(maxLevelIndex);
            children.insert(subChildren.begin(), subChildren.end());
        }
        origins = children;
        return children;
    }

};


// We need this to generate sets and for ordering.
bool operator<(const Clause &c1, const Clause &c2) { return c1.clause < c2.clause; }

bool operator==(const Clause &c1, const Clause &c2) { return c1.clause == c2.clause; }

bool operator<(const EntryVMTF &e1, const EntryVMTF &e2) { return e1.counter < e2.counter; }

bool operator>(const EntryVMTF &e1, const EntryVMTF &e2) { return e1.counter > e2.counter; }

bool operator==(const EntryVMTF &e1, const EntryVMTF &e2) { return e1.literal == e2.literal; }

bool compareEntryPointerAscending(const EntryVMTF *e1, const EntryVMTF *e2) {
    if (e1->counter == e2->counter) {
        if (e1->counter2 == e2->counter2)
            return e1->literal < e2->literal;
        else
            return e1->counter2 > e2->counter2;
    }
    return e1->counter > e2->counter;
}

bool compareEntryPointerDescending(const EntryVMTF *e1, const EntryVMTF *e2) {
    if (e1->counter == e2->counter) {
        if (e1->counter2 == e2->counter2)
            return e1->literal < e2->literal;
        else
            return e1->counter2 < e2->counter2;
    }
    return e1->counter < e2->counter;
}

struct EntryPointer {
    bool operator()(const EntryVMTF *e1, const EntryVMTF *e2) const {
        return compareEntryPointerDescending(e1, e2);
    }
};


bool operator<(const Node &n1, const Node &n2) {
    if (n1.level == n2.level)
        return abs(n1.literal) < abs(n2.literal);
    return n1.level < n2.level;
}

template<class T>
vector<T *> setToSortedVector(const set<T *> &container) {
    vector<T *> container_(container.begin(), container.end());
    sort(container_.begin(), container_.end());
    return container_;
}

template<class T>
vector<T> setToSortedVector(const set<T> &container) {
    vector<T> container_(container.begin(), container.end());
    sort(container_.begin(), container_.end());
    return container_;
}

template<class T>
vector<T> unorderedSetToSortedVector(const unordered_set<T> &container) {
    vector<T> container_(container.begin(), container.end());
    sort(container_.begin(), container_.end());
    return container_;
}

/*
 * Implication graph.
 * Here we define the data structure (and its respective operations) for the implication graph.
 * Each Node stores an edge list of implications.
 */
struct ImplicationGraph {
    vector<Clause> originalCNF;
    unsigned int maxLevelIndex = 0;
    unsigned int assertionLevel = 0;
    unordered_map<int, Node *> nodes;
    vector<int> conflictClause = {};

    explicit ImplicationGraph(vector<Clause> originalCNF) { this->originalCNF = std::move(originalCNF); }

    void addLiteralToGraph(int literal, bool implied) {
        if (!implied)
            ++maxLevelIndex;
        nodes[literal] = new Node(literal, maxLevelIndex);
        assertionLevel = maxLevelIndex;
    }

    void addReasonToLiteral(int literal, const set<Node *> &reason) {
        nodes[literal]->reasons.insert(reason.begin(), reason.end());
        nodes[literal]->updateReasoning();
    }

    set<Node *> getAllNodes() {
        set<Node *> nodes_;
        for (auto pair : nodes)
            nodes_.insert(pair.second);
        return nodes_;
    }

    void printImplicationGraph() {
        cout << "\n======================================\n";
        vector<Node> nodes_;
        for (auto pair : nodes)
            nodes_.push_back(*pair.second);
        sort(nodes_.begin(), nodes_.end());
        for (const auto &node : nodes_) {
            cout << node.level << "[" << node.literal << "] <=";
            for (auto v : setToSortedVector(node.reasons))
                cout << v->literal << " (" << v->level << ") ";
            cout << " => ";
            for (auto v : setToSortedVector(node.implications))
                cout << " " << v->literal << " (" << v->level << ") ";
            cout << "\n";
        }
        cout << "\n======================================\n";

    }

    // When adding a new solution results in UNSAT, this function is called.
    // Return the "assertionLevel".
    set<Node *> handleConflict(Clause *clause) {
        set<Node *> backtrackNodes;
        set<Node *> cut;
        vector<int> cc;
        // Get nodes to be deleted
        // Find asserting cut.
        for (auto literal : clause->originalClause) {
            Node *node = nodes[-literal];
            auto children = node->getChildrenUpperLimit(maxLevelIndex);
            cut.insert(children.begin(), children.end());
        }
        assertionLevel = 0;
        for (auto edge : cut) {
            if (edge->level < maxLevelIndex)
                assertionLevel = max(assertionLevel, edge->level);
        }
        for (auto n : getAllNodes()) {
            if (n->level > assertionLevel)
                backtrackNodes.insert(n);
        }
        // Add negated literals.
        for (auto node : cut)
            cc.push_back(-1 * node->literal);
        // Add conflict clause. Sort to make it deterministic as sets are undeterministic.
        sort(cc.begin(), cc.end());
        conflictClause = cc;

        if (proof) {
            for (auto n : cc) {
                proofFile << n << " ";
            }

            proofFile << 0 << "\n";
        }

        maxLevelIndex = assertionLevel;
        return backtrackNodes;
    }


    /* Deletes a node and from all its implications. */
    void deleteNode(Node *node) {
        nodes.erase(node->literal);
        for (auto imp : node->implications) {
            imp->reasons.erase(node);
            imp->origins.clear();
        }
        for (auto imp : node->reasons)
            imp->implications.erase(node);
    }
};

/**
 * The main data structure used to encode the SAT problem.
 * cnf: stores a CNF in form of a list of lists.
 * clausesRemaining: The indexes of the remaining clauses (that are not fulfilled yet).
 * unassignedVars: A set of variables that have no assignment yet.
 * resolutions: Store the resolutions. Since order matters (LIFO), we use a stack.
 * watchedLiteralToClause: Mapping from literal to its occurrence in the respective clauses.
 * unsat: Is the formula UNSAT?
 * algorithm: Reference to the underlying algorithm variant.
 */
struct Data {
    vector<Clause> cnf;
    ImplicationGraph *implicationGraph;
    set<int> clausesRemaining;
    unordered_set<int> assignedVars;
    unordered_set<int> unassignedVars;
    stack<vector<int>> resolutions;
    unordered_map<int, vector<int>> watchedLiteralToClause;
    unordered_map<int, set<int>> watchedLiteralToClauseFull;
    bool falsified = false;
    bool unsat = false;
    int hitLevelZeroLit = 0;
    int hitLevelZeroCount = 0;
    Algorithm::Version algorithm;
    map<int, EntryVMTF *> mappingVMTF;
    vector<EntryVMTF *> vmtf;
    vector<int> fixedOrder;
    set<Node *> backtrackNodes;
    unordered_set<int> phaseSaving;

    /* Updates information for the data object */
    void updateClauseInformation(bool reset = false) {
        unassignedVars.clear();
        watchedLiteralToClause.clear();
        watchedLiteralToClauseFull.clear();
        clausesRemaining.clear();
        for (int i = 0; i < cnf.size(); ++i) {
            if (cnf[i].discarded)
                continue;
            if (reset)
                cnf[i].clause = cnf[i].originalClause;
            for (auto v : cnf[i].originalClause)
                watchedLiteralToClauseFull[abs(v)].insert(i);
            applySolution(&cnf[i]);
            if (cnf[i].clause.empty()) {
                if (falsified) {
                    clausesRemaining.insert(i);
                    return;
                } else continue;
            }
            clausesRemaining.insert(i);
            for (auto v : cnf[i].clause) {
                this->unassignedVars.insert(abs(v));
                this->watchedLiteralToClause[v].push_back(i);
            }
        }
    }

    /* Resets the data object */
    void updateVMTF() {
        vmtf.clear();
        fixedOrder.clear();
        vector<EntryVMTF *> vars;
        for (auto var : unassignedVars) {
            int c = getLiteralCount(-var) * getLiteralCount(var);
            vars.push_back(new EntryVMTF(var, getLiteralCount(var), c));
            vars.push_back(new EntryVMTF(-var, getLiteralCount(-var), c));
        }
        sort(vars.begin(), vars.end(), compareEntryPointerAscending);
        // We add to fixedOrder now since vmtf is sorted by count.
        for (auto v : vars) {
            mappingVMTF[v->literal] = v;
            mappingVMTF[v->literal]->counter = 0;
            vmtf.push_back(mappingVMTF[v->literal]);
            fixedOrder.push_back(v->literal);
        }
    }

/* Constructor for the data structure. */
    explicit Data(ImplicationGraph *implicationGraph, Algorithm::Version algorithm) {
        this->implicationGraph = implicationGraph;
        this->cnf = implicationGraph->originalCNF;
        this->algorithm = algorithm;
        updateClauseInformation();
        updateVMTF();
    }

    /* Delete added conflict clauses with <50% assigned vars and more than 8 vars
     * if the number of added conflict clauses is more than twice than number of starting
     * clauses. */
    void clauseDeletion() {
        int orgSize = implicationGraph->originalCNF.size();
        bool deleteClauses = cnf.size() - orgSize > 2 * orgSize;
        for (int i = orgSize; i < cnf.size(); ++i) {
            if (deleteClauses && cnf[i].conflictClause && !cnf[i].discarded && cnf[i].clause.size() > 8 &&
                float(cnf[i].clause.size()) / cnf[i].originalClause.size() > 0.55) {
                discardClause(i, false);
            }
        }
    }

    /* Returns all non-original clauses (resolutions + conflict clauses) */
    vector<Clause> getNonOriginalClauses() {
        vector<Clause> clauses(cnf.begin() + implicationGraph->originalCNF.size(), cnf.end());
        return clauses;
    }

    /* Returns all original clauses */
    vector<Clause> getOriginalClauses() const {
        vector<Clause> clauses(cnf.begin(), cnf.begin() + implicationGraph->originalCNF.size());
        return clauses;
    }

    /* Restores the original clauses. */
    void nonChronologicalBacktracking() {
        if (unsat) return;
        // while (!resolutions.empty())
        //     resolutions.pop();
        set<int> clausesToBacktrack;
        for (auto node : backtrackNodes) {
            // cout << node->literal << " ";
            implicationGraph->deleteNode(node);
            assignedVars.erase(node->literal);
            clausesToBacktrack.insert(watchedLiteralToClauseFull[abs(node->literal)].begin(),
                                      watchedLiteralToClauseFull[abs(node->literal)].end());
        }
        falsified = false;
        backtrackNodes.clear();
        updateClauses(clausesToBacktrack);
        clauseDeletion();
        addClause(Clause(implicationGraph->conflictClause, true));
        //updateClauseInformation(true);
    }

    /* Returns true if unsat or test_all.
     * A function is set to be test_all if clausesRemaining.empty is true, that is, if all
     * clauses are satisfied */
    bool canAbort() const {
        return unsat || clausesRemaining.empty();
    }

    /* Returns all clauses which are not yet satisfied. */
    vector<Clause> getRemainingClauses() {
        vector<Clause> temp;
        for (auto i: clausesRemaining)
            temp.push_back(cnf[i]);
        return temp;
    }

    /* Return the number of times a given literal occurs in unsatisfied clauses. */
    int getLiteralCount(int v) {
        if (!watchedLiteralToClause.count(v))
            return 0;
        return this->watchedLiteralToClause[v].size();
    }

    /* Applies a solution to a clause (i.e removes potential negated literals). */
    void applySolution(Clause *c) {
        if (falsified || c->clause.empty()) return;
        for (auto v : assignedVars) {
            if (count(c->clause.begin(), c->clause.end(), v)) {
                c->clause.clear();
                return;
            }
            c->clause.erase(remove(c->clause.begin(), c->clause.end(), -v), c->clause.end());
            if (c->clause.empty()) {
                setFalsified(c);
                cout << "F-APPLY ";
                unsat = true;
                return;
            }
        }
    }

    void setFalsified(Clause *clause) {
        falsified = true;
        backtrackNodes = implicationGraph->handleConflict(clause);
        // Update "variable move to front" (VMTF) heuristic.
        vector<EntryVMTF *> entries;
        priority_queue<EntryVMTF *, vector<EntryVMTF *>, EntryPointer> priorityQueue;
        for (auto v : implicationGraph->conflictClause) {
            mappingVMTF[-v]->counter += 1;
            priorityQueue.push(mappingVMTF[-v]);
        }
        if (algorithm != Algorithm::Version::HEU_LIT) {
            int n = 0;
            stack<EntryVMTF *> toMove;
            while (!priorityQueue.empty() && ++n <= 8) {
                EntryVMTF *entry = priorityQueue.top();
                priorityQueue.pop();
                toMove.push(entry);
            }
            while (!toMove.empty()) {
                EntryVMTF *entry = toMove.top();
                toMove.pop();
                int index = find(vmtf.begin(), vmtf.end(), entry) - vmtf.begin();
                moveToFront(vmtf, index);
            }
        }
    }

    /* Updates a subset of clause information. */
    void updateClauses(const set<int> &clauses) {
        for (int i : clauses) {
            cnf[i].clause = cnf[i].originalClause;
            applySolution(&cnf[i]);
            if (cnf[i].clause.empty())
                continue;
            clausesRemaining.insert(i);
            for (auto v : cnf[i].clause) {
                this->unassignedVars.insert(abs(v));
                if (find(watchedLiteralToClause[v].begin(), watchedLiteralToClause[v].end(), i)
                    == watchedLiteralToClause[v].end())
                    this->watchedLiteralToClause[v].push_back(i);
            }
        }
    }

    /* Add a new clause and update information accordingly. */
    void addClause(const Clause &c_) {
        cnf.emplace_back(c_);
        if (unsat) { return; }
        Clause *c = &cnf.back();
        for (int v : c->originalClause)
            watchedLiteralToClauseFull[abs(v)].insert(cnf.size() - 1);
        applySolution(c);
        //Re-reference literals.
        for (int v : c->clause) {
            watchedLiteralToClause[v].push_back(cnf.size() - 1);
            unassignedVars.insert(abs(v));
        }
        if (unsat || !c->clause.empty())
            clausesRemaining.insert(cnf.size() - 1);
        else if (!unsat && c->clause.size() == 1)
            addSolution(c->clause.front());
    }

    /* Sets a clasue to nothing */
    void emptyClause(int index) {
        cnf[index].clause.clear();
        for (int v : cnf[index].originalClause)
            watchedLiteralToClauseFull[abs(v)].erase(index);
        cnf[index].originalClause.clear();
    }

/* Removes a clause from the unsatisfied list, but updates all parameters accordingly. */
    void discardClause(int index, bool keep = true) {
        clausesRemaining.erase(index);
        if (!keep) {
            emptyClause(index);
        }
        cnf[index].discarded = true;
        for (auto v : cnf[index].clause) {
            watchedLiteralToClause[v].erase(remove(watchedLiteralToClause[v].begin(),
                                                   watchedLiteralToClause[v].end(), index),
                                            watchedLiteralToClause[v].end());
        }
    }

    /* Adds a literal to the solution list, i.e assigns a ground-truth to a variable. */
    void addSolution(int v, const set<Node *> &reason = {}, int imp = 0) {
        // cout << "(" << v << "-> " << implicationGraph->maxLevelIndex << ")";
        if (assignedVars.count(v) || falsified)
            return;
        // The counter keeps track on how many assignments we have done.
        COUNTER++;
        // cout << v << " ";
        // Extend implication tree only if the literal is not contained!
        bool implied = !reason.empty();
        implicationGraph->addLiteralToGraph(v, implied);
        if (implied)
            implicationGraph->addReasonToLiteral(v, reason);
        //else cout << ".";
        unassignedVars.erase(abs(v));
        assignedVars.insert(v);
        //Remove satisfied clauses.
        vector<int> clauses(watchedLiteralToClause[v]);
        for (auto i : clauses) {
            clausesRemaining.erase(i);
            for (int v2 : cnf[i].clause)
                watchedLiteralToClause[v2].erase(remove(watchedLiteralToClause[v2].begin(),
                                                        watchedLiteralToClause[v2].end(), i),
                                                 watchedLiteralToClause[v2].end());
        }
        vector<pair<int, set<Node *>>> impliedSolutions;
        //Remove negated literal from clauses.
        for (auto i : watchedLiteralToClause[-v]) {
            cnf[i].clause.erase(remove(cnf[i].clause.begin(), cnf[i].clause.end(), -v),
                                cnf[i].clause.end());
            if (cnf[i].clause.empty() && count(clausesRemaining.begin(), clausesRemaining.end(), i)) {
                setFalsified(&cnf[i]); // Falsified !!!!
                // cout << "F-NEGATED " << -v;
                return;
            }
            if (cnf[i].clause.size() == 1) {
                int v2 = cnf[i].clause.front();
                set<Node *> reason_;
                for (auto lit : cnf[i].originalClause) {
                    if (lit != v2)
                        reason_.insert(implicationGraph->nodes[-lit]);
                }
                impliedSolutions.emplace_back(v2, reason_);
            }
        }
        // First clear, then propagate reasons.
        for (const auto &p : impliedSolutions) {
            if (!assignedVars.count(p.first))
                addSolution(p.first, p.second);
            if (falsified) { return; }
        }
        watchedLiteralToClause[-v].clear();
        watchedLiteralToClause[v].clear();
    }

    /* Adds multiple literals to the solution list, i.e assigns ground-truths to variables. */
    void addSolutions(const unordered_set<int> &alpha) {
        for (auto v : alpha) {
            addSolution(v, set<struct Node *>());
            if (falsified) { return; }
        }
    }

    /* Performs the resolution rule as stated in the script for a given variable.
     * Assumes the literal and its negation occur both exactly once.
     */
    void resolve(int literal) {
        set<vector<int>> newClauses;
        vector<int> a_;
        for (auto a : watchedLiteralToClause[literal]) {
            if (cnf[a].clause.size() > 1 && !count(cnf[a].clause.begin(), cnf[a].clause.end(), -literal))
                a_.push_back(a);
        }
        int b = watchedLiteralToClause[-literal][0];
        // Check if resulting resolutions are tautologies, then don't resolve.
        if (a_.empty() || count(cnf[b].clause.begin(), cnf[b].clause.end(), literal))
            return;
        // Discard resolved clause.
        discardClause(b);
        // Put the negated literal at the end of the vector (so we can access it easier later on).
        cnf[b].clause.erase(remove(cnf[b].clause.begin(), cnf[b].clause.end(), -literal), cnf[b].clause.end());
        cnf[b].clause.push_back(-literal);
        // Add to the resolution history.
        resolutions.push(cnf[b].clause);
        // Resolve clauses.
        for (int a : a_) {
            discardClause(a);
            // Check if equal.
            if (count(cnf[a].clause.begin(), cnf[a].clause.end(), -literal))
                continue;
            vector<int> newClause(cnf[a].originalClause);
            unassignedVars.erase(abs(literal));
            // Merge both clauses.
            newClause.insert(newClause.end(), cnf[b].originalClause.begin(), cnf[b].originalClause.end());
            // Delete literals from resolved clause and the original clause.
            newClause.erase(remove(newClause.begin(), newClause.end(), literal), newClause.end());
            newClause.erase(remove(newClause.begin(), newClause.end(), -literal), newClause.end());
            // Remove duplicates.
            sort(newClause.begin(), newClause.end());
            newClause.erase(unique(newClause.begin(), newClause.end()), newClause.end());
            newClauses.insert(newClause);
            emptyClause(a);
        }
        emptyClause(b);
        // Clear literal(s).
        watchedLiteralToClause[-literal].clear();
        watchedLiteralToClause[literal].clear();
        for (const auto &c : newClauses)
            addClause(Clause(c));
    }
};

void preprocess(Data *pData);

void preprocess2(Data *pData);

/* Eliminates clauses that contain both, a variable and its negation, in the same clause. */
void eliminateTautologies(Data *data) {
    if (data->falsified) { return; }
    set<int> cnf(data->clausesRemaining);
    for (auto i : cnf) {
        for (auto c : data->cnf[i].clause) {
            if (find(data->cnf[i].clause.begin(), data->cnf[i].clause.end(), -c) != data->cnf[i].clause.end()) {
                //If we have a tautology we can ignore the clause,
                // but do not assign any new variable to the solution!
                data->discardClause(i);
                break;
            }
        }
    }
}

/* Reads a dimacsCNF file from a given path. */
vector<Clause> loadDimacsCnf(const string &path) {
    // cout << "Loading Dimacs-file at \"" << path << "\"." << endl;
    ifstream file(path);
    string str;
    int nLiterals = 0;
    vector<Clause> cnf;
    vector<int> numbers;
    while (getline(file, str)) {
        if (str[0] != 'c' && str[0] != 'p' && !str.empty()) {
            stringstream iss(str);
            int number;
            while (iss >> number) {
                if (number == 0) {
                    Clause clause = Clause(numbers);
                    cnf.push_back(clause);
                    nLiterals += numbers.size();
                    numbers.clear();
                } else
                    numbers.push_back(number);
            }
        }
    }
    // cout << "Done! (Clauses: " << cnf.size() << " | Literals " << nLiterals << ")." << endl;
    return cnf;
}

/* Transforms any CNF to 3-SAT.
 * We do not use this in our version, since the resolution rule sort of "undoes" the procedure. */
vector<Clause> to3SAT(const vector<Clause> &cnf) {
    cout << "Transforming CNF to 3-SAT..." << endl;
    vector<vector<int>> threeSat;
    int maxVar = 0;
    for (const auto &clause : cnf)
        for (int literal : clause.clause)
            maxVar = max(abs(literal), maxVar);
    for (auto c : cnf) {
        if (c.clause.size() <= 3)
            threeSat.push_back(c.clause);
        else {
            vector<int> v{c.clause[0], c.clause[1], ++maxVar};
            threeSat.push_back(v);
            for (int i = 2; i < c.clause.size() - 2; i++) {
                vector<int> v1{-maxVar, c.clause[i], ++maxVar};
                threeSat.push_back(v1);
            }
            vector<int> v2{-maxVar, c.clause[c.clause.size() - 2],
                           c.clause[c.clause.size() - 1]};
            threeSat.push_back(v2);
        }
    }
    cout << "Done! (Clauses old: " << cnf.size() << " | Clauses new: " << threeSat.size() << ")."
         << endl;
    vector<Clause> clauses;
    for (auto c : threeSat)
        clauses.push_back(Clause(c));
    return clauses;
}

/* Removes clauses that contain only one literal and assigns those as solutions.
 * This also adds reasons to the implication graph. */
void removeUnitClauses(Data *data) {
    if (data->falsified) { return; }
    // cout << "Determining and removing unit clauses and literals." << endl;
    set<int> cnf(data->clausesRemaining);
    for (auto i : cnf)
        if (data->cnf[i].clause.size() == 1) {
            int literal = data->cnf[i].clause[0];
            set<Node *> reason;
            for (auto lit : data->cnf[i].originalClause) {
                if (lit != literal)
                    reason.insert(data->implicationGraph->nodes[-lit]);
            }
            data->addSolution(literal, reason);
            if (data->falsified)
                return;
        }
}

/* Determines and removes pure literals from clauses, and respectively includes those as solutions. */
void removePureLiterals(Data *data, const set<Node *> &reason = {}) {
    if (data->falsified) { return; }
    // cout << "Detecting and removing pure literals." << endl;
    //unassignedVars stores only the absolute variable values.
    for (auto v : unorderedSetToSortedVector(data->unassignedVars)) {
        int a = data->getLiteralCount(v);
        int b = data->getLiteralCount(-v);
        if (b == 0)
            data->addSolution(v, reason);
        else if (a == 0)
            data->addSolution(-v, reason);
        if (data->falsified)
            return;
    }
}

/* Performs the resolution rule, as states in the script (which is similar to combining clauses).
 * Must be called last but before subsumption when used in conjunction with other preprocessing reductions!
 */
void performResolutionRule(Data *data) {
    if (data->falsified) { return; }
    unordered_set<int> vars(data->unassignedVars);
    for (auto literal : vars) {
        if (data->getLiteralCount(literal) == 1 && data->getLiteralCount(-literal) > 0) {
            data->resolve(-literal);
        } else if (data->getLiteralCount(-literal) == 1 && data->getLiteralCount(literal) > 0) {
            data->resolve(literal);
        }
    }
}

/* Checks for autarkic clauses, as stated in the script. */
bool isAutarkic(const vector<Clause> &cnf, unordered_set<int> alpha) {
    for (const Clause &c : cnf) {
        bool conflicts = false;
        bool satisfies = false;
        for (int v : c.clause) {
            if (alpha.find(v) != alpha.end())
                satisfies = true;
            else if (alpha.find(-v) != alpha.end())
                conflicts = true;
        }
        if (conflicts && !satisfies)
            return false;
    }
    return true;
}

/* We will use a third check/test to make sure that our solution is correct. Here, we scrutinize
 * whether the intersection of the solution and each clause is non-empty.
 */
bool verifySolution(const vector<Clause> &cnf, const unordered_set<int> &alpha) {
    for (const Clause &c : cnf) {
        bool correct = false;
        for (int v : c.originalClause) {
            if (alpha.count(v)) {
                correct = true;
                break;
            }
        }
        if (!correct) {
            return false;
        }
    }
    return true;
}

/* Returns the smallest of all clauses in a given cnf. */
Clause getSmallestClause(const vector<Clause> &cnf) {
    int bestV = -1;
    Clause bestK = Clause({});
    for (const auto &c : cnf)
        if ((bestV > c.clause.size() || bestV == -1) && !c.clause.empty()) {
            bestK = c;
            bestV = c.clause.size();
        }
    return bestK;
}

/* Returns a set of all variables in a cnf. */
unordered_set<int> getVariables(const vector<Clause> &cnf, bool absolute = false) {
    unordered_set<int> vars;
    for (const auto &clause : cnf)
        for (auto c : clause.clause) {
            if (absolute)
                vars.insert(abs(c));
            else if (vars.find(-c) == vars.end())
                vars.insert(c);
        }
    return vars;
}

/* Performs the subsumation rule. */
void removeSubsumedClauses(Data *data) {
    if (data->falsified) { return; }
    set<int> cnfUnsat(data->clausesRemaining);
    vector<Clause> cnf(data->cnf);
    for (int i : cnfUnsat)
        sort(cnf[i].clause.begin(), cnf[i].clause.end());
    for (auto largeClause : cnfUnsat) {
        for (auto clause : cnfUnsat) {
            if (cnf[largeClause].clause.size() <= cnf[clause].clause.size())
                continue;
            if (includes(cnf[largeClause].clause.begin(), cnf[largeClause].clause.end(),
                         cnf[clause].clause.begin(), cnf[clause].clause.end())) {
                data->discardClause(largeClause, false);
            }
        }
    }
}

/* Sort unsat clauses, used for heuristics when there exist multiple "smallest" clauses of the same size.
 * Here, the number of variable (not literal) occurrence is of importance!
 * We first need to sort clauses, the the order within the clauses! */
vector<Clause> sortUnsatClausesVariables(Data *data, int order = -1) {
    vector<tuple<int, int, int>> cnfOrdered;
    for (int i : data->clausesRemaining) {
        int v = 0;
        int v2 = 0;
        for (auto item : data->cnf[i].clause) {
            v += data->getLiteralCount(item) + data->getLiteralCount(-item);
            v2 += data->getLiteralCount(item) * data->getLiteralCount(-item);
        }
        v *= order;
        v2 *= order;
        cnfOrdered.emplace_back(v, v2, i);
    }
    sort(cnfOrdered.begin(), cnfOrdered.end());

    vector<Clause> cnf;
    for (auto p :cnfOrdered) {
        Clause clause = data->cnf[get<2>(p)];
        sort(clause.clause.begin(), clause.clause.end(), [&data](int x, int y) {
            int a = data->getLiteralCount(x);
            int b = data->getLiteralCount(y);
            int a2 = data->getLiteralCount(-x);
            int b2 = data->getLiteralCount(-y);
            if (a + a2 != b + b2)
                return a + a2 > b + b2;
            else
                return a * a2 > b * b2;
        });
        cnf.push_back(clause);
    }
    return cnf;
}

/* The "variable move to front" (VMTF) heuristic! */
int heuristicVMTF(Data *data) {
    for (auto entry : data->vmtf) {
        if (data->unassignedVars.count(entry->literal))
            return entry->literal;
    }
    // We will not reach that.
    return 0;
}

/* Pick a variable following a fixed order! */
int heuristicFixedOrder(Data *data) {
    int v = 0;
    for (int i = 0; i < data->fixedOrder.size(); i++) {
        if (data->unassignedVars.count(data->fixedOrder[i])) {
            v = data->fixedOrder[i];
            break;
        }
    }
    return v;
}

/* Main logic of the test_all solver; used for recursion. */
void solveSAT(Data *data) {
    int v;
    removeUnitClauses(data);
    if (!data->falsified && !data->unassignedVars.empty()) {
        //////////////////////////  AUTARKIC CLAUSES TRICK  //////////////////////////
        if (data->algorithm == Algorithm::Version::AUT) {
            vector<Clause> cnf;
            cnf = sortUnsatClausesVariables(data);
            Clause nextClause = getSmallestClause(cnf);
            for (int i = 0; i < nextClause.clause.size(); ++i) {
                unordered_set<int> assignmentNew = {};
                assignmentNew.insert(nextClause.clause[i]);
                for (int j = 0; j < i; ++j)
                    assignmentNew.insert(-nextClause.clause[j]);
                if (isAutarkic(cnf, assignmentNew)) {
                    data->addSolutions(assignmentNew);
                    return;
                }
            }
        }
        ////////////////////////// CORE ALGORITHM  //////////////////////////
        // Heuristics
        if (data->algorithm != Algorithm::Version::HEU_LIT)
            v = heuristicVMTF(data);
        else
            v = heuristicFixedOrder(data);
        // Check for phase saving.
        if (data->phaseSaving.count(-v)) {
            data->phaseSaving.erase(-v);
            v = -v;
        } else
            data->phaseSaving.erase(v);
        // Add literal to solution.
        data->addSolution(v);
        /// PRE-FILTERING:
        if (data->algorithm != Algorithm::Version::NO_PREP && !data->falsified) {
            eliminateTautologies(data);
            removePureLiterals(data);
        }
    }
    if (data->falsified) {
        ++RESTART_COUNTER;
        // cout << "[" << data->implicationGraph->assertionLevel << "]";
        if (data->implicationGraph->assertionLevel == 0) {
            if (abs(data->hitLevelZeroLit) == abs(v))
                data->hitLevelZeroCount += 1;
            else
                data->hitLevelZeroCount = 0;
            data->hitLevelZeroLit = abs(v);
            data->unsat = data->hitLevelZeroCount > 2;
        }
        data->assignedVars.erase(v);
        data->nonChronologicalBacktracking();
    }
}

/* Starts the recursive test_all-solver calls and sotres data accordingly in files. */
int solveDimacs(const string &path, Algorithm::Version algorithm) {
    bool sat;
    clock_t tStart = clock();
    srand(unsigned(time(nullptr)));
    cout << "Path: " << path << endl;
    cout << "Algorithm: " << Algorithm::getVersionName(algorithm) << endl;
    cout << "Generating data structure.";
    vector<Clause> cnf = loadDimacsCnf(path);
    const unordered_set<int> &origVars = getVariables(cnf);
    // cnf = to3SAT(cnf); //Worsens performance!
    ImplicationGraph implicationGraph = ImplicationGraph(cnf);
    Data dataOriginal = Data(&implicationGraph, algorithm);
    Data data(dataOriginal);
    ///////// SAT SOLVER LOOP ////////
    COUNTER = 0;
    RESTART_COUNTER = 0;
    RESTARTS = 0;
    // Logic loop.
    preprocess(&data);
    cout << "\nSolving <";
    if (data.falsified)
        data.unsat = true;
    int m = 200;
    int k = max(m, min(int(origVars.size()), int(implicationGraph.originalCNF.size())));
    while (!data.canAbort()) {
        // Resetting & full preprocessing.
        if ((RESTART_COUNTER + 1) % m == 0)
            cout << "|";
        if (RESTART_COUNTER > ((m * RESTARTS) + k)) {
            cout << "/";
            RESTART_COUNTER = 0;
            ++RESTARTS;
            data.hitLevelZeroLit = false;
            data.phaseSaving = data.assignedVars;
            data.backtrackNodes = data.implicationGraph->getAllNodes();
            data.nonChronologicalBacktracking();
            preprocess2(&data);
        }
        // Logic.
        solveSAT(&data);
    }
    ////////////////////////////////
    cout << ">";
    vector<int> solution;
    if (!data.unsat) {
        for (int v : data.assignedVars)
            if (origVars.find(v) != origVars.end() || origVars.find(-v) != origVars.end())
                solution.push_back(v);

        // Add resolved variables accordingly.
        while (!data.resolutions.empty()) {
            auto vec = data.resolutions.top();
            int literal = vec.back();
            unordered_set<int> alpha(solution.begin(), solution.end());
            if (vec.size() > 1) {
                if (removeSatisfiedClauses({Clause(vec)}, alpha).empty())
                    solution.push_back(-literal);
                else
                    solution.push_back(literal);
            } else
                solution.push_back(literal);
            data.resolutions.pop();
        }
        // Add variables that can have either ground truth assignment (i.e pos/neg).
        // We will assign them a positive ground truth per default.
        for (auto v : data.unassignedVars)
            solution.push_back(v);
        // Print solution.
        cout << "\nSOLVED:\n";
        sort(solution.begin(), solution.end(), [](int x, int y) { return abs(x) < abs(y); });
        printVector(solution);
        cout << "\n";
        sat = true;
    } else {
        cout << "\nFORMULA UNSAT!" << endl;
        sat = false;
    }
    if (algorithm == Algorithm::DEFAULT) {
        int beginIdx = path.rfind('/');
        std::string filename = path.substr(beginIdx + 1);
        solutionFile.open(filename);
        if (sat) {
            solutionFile << "s SATISFIABLE" << "\n";
            solutionFile << "v ";
            for (int j : solution) {
                solutionFile << j << " ";
            }
            solutionFile << 0;
        } else {

            solutionFile << "s UNSATISFIABLE" << "\n";
        }
        solutionFile.close();
    }

    long time = (clock() - tStart);
    textFileTimes << "," << time;

    cout << "[Steps: " << COUNTER << "] ";
    textFileSteps << "," << COUNTER;

    printf("[Execution time: %.2fs] ", (double) (clock() - tStart) / CLOCKS_PER_SEC);
    cout << "[Clauses added: " << data.cnf.size() - dataOriginal.cnf.size() << " ]\n";
    cout << "===============================================================" << endl;
    unordered_set<int> solutionCheck(solution.begin(), solution.end());
    return data.unsat ||
           (verifySolution(cnf, solutionCheck) && removeSatisfiedClauses(cnf, solutionCheck).empty());
}

/* Applies preprocessing to a data object */
void preprocess(Data *data) {
    eliminateTautologies(data);
    removeUnitClauses(data);
    removePureLiterals(data);
    removeSubsumedClauses(data);
    performResolutionRule(data);
}

/* Applies preprocessing to a data object */
void preprocess2(Data *data) {
    eliminateTautologies(data);
    removeUnitClauses(data);
    removePureLiterals(data);
    removeSubsumedClauses(data);
    performResolutionRule(data);
}

/* Helper function to read in all files in a given directory. */
vector<string> getTestFiles(const char *directory) {
    vector<string> paths;
    DIR *dir;
    struct dirent *ent;
    if ((dir = opendir(directory)) != nullptr) {
        while ((ent = readdir(dir)) != nullptr) {
            string path(ent->d_name);
            if (path.size() < 3)
                continue;
            string d(directory);
            d.append("/" + path);
            paths.emplace_back(d);
        }
        closedir(dir);
    }
    return paths;
}

/* Main loop; loads in all /test files and starts the solving process. */
int main(int argc, char **argv) {

    textFileTimes.open("times.csv");
    textFileSteps.open("steps.csv");
    textFileTimes << "Algorithm";
    textFileSteps << "Algorithm";
    vector<string> paths;
    vector<string> paths2;
    vector<string> paths3;

    for (int i = 0; i < argc; i++) {
        if (strcmp(argv[i], "proof") == 0) {
            proof = true;
        }
    }

    if (argc < 2) {
        cout << "Path needs to be provided as command line argument!";
        cout << "\n\nPress any key to exit...";
        return 0;
    }
    if (strcmp(argv[1], "-file") == 0) {
        paths = {argv[2]};

    }
    if (strcmp(argv[1], "-dir") == 0) {

        paths = getTestFiles(argv[2]);

        if (argc == 4) {
            paths2 = getTestFiles(argv[3]);
            paths.insert(paths.end(), paths2.begin(), paths2.end());
        }

    }

    // paths = {"../inputs/test_all/par16-1-c.cnf"};
    // paths = getTestFiles("../inputs/test_all");

    bool correct = true;
    for (int i = 0; i < paths.size(); ++i) {
        textFileTimes << "," << i;
        textFileSteps << "," << i;
    }
    clock_t startingTime = clock();
    unsigned int stepsTotal = 0;
    for (const auto algorithm : Algorithm::Default) {
        textFileTimes << "\n" << Algorithm::getVersionName(algorithm);
        textFileSteps << "\n" << Algorithm::getVersionName(algorithm);
        for (const auto &path : paths) {
            if (proof) {
                int beginIdx = path.rfind('/');
                string filename = path.substr(beginIdx + 1);
                filename = regex_replace(filename, regex("cnf"), "drup");
                proofFile.open(filename);
            }
            correct = correct && solveDimacs(path, algorithm);
            stepsTotal += COUNTER;
            proofFile << 0;
            proofFile.close();
        }
    }

    textFileTimes.close();
    textFileSteps.close();

    cout << "=> Total steps: " << stepsTotal << ".\n";
    // Here we can double check if our solution is actually true, if not, print it!
    // We can do that by feeding in the solution ot the entire CNF and see if it solves it.
    if (!correct) {
        cout << "\nSOMETHING WENT WRONG!";
        if (proof) {
            cout << "\n\nPROOF!";
        }
    } else {
        cout << "\nSOLUTION CORRECT & CHECKED!";
        if (proof) {
            cout << "\n\nPROOF!";
        }
    }

    long endTime = (clock() - startingTime);
    int minutes = (int) endTime / CLOCKS_PER_SEC / 60;
    cout << "\n\n" << minutes << " min. total execution time." << argv[2];
    if (argv[3] != NULL) { cout << " and " << argv[3]; }
    cout << "\n\nPress any key to exit...";
    getchar();
}