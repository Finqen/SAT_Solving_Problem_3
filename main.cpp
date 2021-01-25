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
#include <dirent.h>

using namespace std;

ofstream textFileTimes;
ofstream textFileSteps;
ofstream solutionFile;
unsigned int COUNTER = 0;
// const auto MAX_THREADS = thread::hardware_concurrency();

/* Namespace to define variations of algorithms that bundles names as access points */
namespace Algorithm {
    enum Version {
        DEFAULT, HEU_RAND, NO_AUT, NO_PREP
    };
    // All: Contains all variants
    static const Version All[] = {DEFAULT, NO_AUT, HEU_RAND};
    // Contains only the default variant
    static const Version Default[] = {DEFAULT};
    static const Version NoPP[] = {NO_PREP};


    // Return a more informative string if needed.
    string getVersionName(enum Version algorithm) {
        switch (algorithm) {
            case DEFAULT:
                return "Heuristic Variables";
            case HEU_RAND:
                return "Heuristic Random";
            case NO_AUT:
                return "Not Autartic";
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

/* Data structure for clauses that also stores the original clause */
struct Clause {
    vector<int> clause;
    vector<int> originalClause;

    explicit Clause(const vector<int> &clause) {
        this->clause = clause;
        this->originalClause = clause;
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
    set<Node *> edges;

    explicit Node(int literal, unsigned int level, set<Node *> edges = {}) {
        this->literal = literal;
        this->level = level;
        this->edges = std::move(edges);
    }

    /* Returns childes (i.e edges/cuts) that are do not contain the current level! */
    set<Node *> getNonAssertingChildren(unsigned int maxLevelIndex) {
        set<Node *> children;
        if (level < maxLevelIndex)
            return set({this});
        for (auto edge : edges) {
            auto subChildren = edge->getNonAssertingChildren(maxLevelIndex);
            children.insert(subChildren.begin(), subChildren.end());
        }
        return children;
    }
};


// We need this to generate sets and for ordering.
bool operator<(const Clause &c1, const Clause &c2) { return c1.clause < c2.clause; }

bool operator==(const Clause &c1, const Clause &c2) { return c1.clause == c2.clause; }

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
    unordered_map<int, Node *> nodes;
    set<Clause> conflictClauses;

    explicit ImplicationGraph(vector<Clause> originalCNF) { this->originalCNF = std::move(originalCNF); }

    int getSize() const { return nodes.size(); }

    Node *addSolutionGuess(int literal) {
        nodes[literal] = new Node(literal, ++maxLevelIndex);
        // cout << "\nGuess: " << literal << " (" << nodes[literal]->level << ") ";
        return nodes[literal];
    }

    Node *addImplication(int literal, const set<Node *> &implications) {
        unsigned int maxLevel = 0;
        // Also, get the highest implication level.
        for (auto imp : implications)
            maxLevel = max(maxLevel, imp->level);
        nodes[literal] = new Node(literal, maxLevel, implications);
        // cout << "-> " << literal << " (" << nodes[literal]->level << ") ";
        // printVector(implications);
        return nodes[literal];
    }

    // When adding a new solution results in UNSAT, this function is called.
    // Return the "assertionLevel".
    Node *handleConflictClause(Clause *clause) {
        bool asserting = false;
        bool getAssertingChildren = false;
        Node *assertionNode = nullptr;
        set<Node *> cut;
        // Find basic cut
        // TODO: Find more cuts, e.g using heuristics
        for (auto literal : clause->originalClause) {
            Node *node = nodes[-literal];
            set<Node *> edges = node->edges;
            if (edges.empty())
                cut.insert(node);
            else
                copy(edges.begin(), edges.end(), inserter(cut, cut.end()));
        }
        set<Node *> cutAsserting;
        for (auto edge : cut) {
            // Check if clause is asserting!
            if (edge->level == maxLevelIndex) {
                if (!asserting)
                    asserting = true;
                else
                    getAssertingChildren = true;
            }
            cutAsserting.insert(edge);
        }
        //Check for asserting conflict clause, which should be guaranteed by the above function.
        if (!asserting)
            return nullptr;
        // Get children if necessary.
        if (getAssertingChildren) {
            for (auto edge : cutAsserting) {
                auto children = edge->getNonAssertingChildren(maxLevelIndex);
                for (auto e : children)
                    cutAsserting.insert(e);
            }
        }
        // Get the assertion level.
        for (auto edge : cutAsserting) {
            if ((nullptr == assertionNode || edge->level > assertionNode->level) && edge->level < maxLevelIndex)
                assertionNode = edge;
        }
        vector<int> c;
        // Add negated literals
        for (auto node : cutAsserting)
            c.push_back(-1 * node->literal);
        // Add conflict clause
        Clause conflictClause(c);
        conflictClauses.insert(conflictClause);
        return assertionNode;
    }
};

/**
 * The main data structure used to encode the SAT problem.
 * cnf: stores a CNF in form of a list of lists.
 * clausesRemaining: The indexes of the remaining clauses (that are not fulfilled yet).
 * unassignedVars: A set of variables that have no assignment yet.
 * resolutions: Store the resolutions. Since order matters (LIFO), we use a stack.
 * literalToClause: Mapping from literal to its occurrence in the respective clauses.
 * unsat: Is the formula UNSAT?
 * algorithm: Reference to the underlying algorithm variant.
 */
struct Data {
    vector<Clause> cnf;
    ImplicationGraph *implicationGraph;
    vector<int> clausesRemaining;
    unordered_set<int> assignedVars;
    unordered_set<int> unassignedVars;
    stack<vector<int>> resolutions;
    set<Node *> solutionHistory;
    unordered_map<int, vector<int>> literalToClause;
    bool falsified = false;
    bool unsat = false;
    Algorithm::Version algorithm;
    Node *assertionNode = nullptr;
    stack<Node *> assertionHistory;

    /* Constructor for the data structure. */
    explicit Data(ImplicationGraph *implicationGraph, Algorithm::Version algorithm) {
        this->implicationGraph = implicationGraph;
        this->cnf = implicationGraph->originalCNF;
        this->algorithm = algorithm;
        for (int i = 0; i < cnf.size(); ++i) {
            clausesRemaining.push_back(i);
            for (auto v : cnf[i].clause) {
                this->unassignedVars.insert(abs(v));
                this->literalToClause[v].push_back(i);
            }
        }
    }

    /* Restores the original clauses. */
    void nonChronologicalBacktracking() {
        // cout << "|";
        if (assertionNode == nullptr) {
            assertionNode = assertionHistory.top();
            assertionHistory.pop();
        }
        while (!resolutions.empty())
            resolutions.pop();
        set<Node *> solutionHistory_(solutionHistory);
        for (auto node : solutionHistory_) {
            // cout << node->literal << "[" << node->level << "]";
            if (node->level >= assertionNode->level) {
                assignedVars.erase(node->literal);
                unassignedVars.insert(abs(node->literal));
                solutionHistory.erase(node);
            }
        }
        falsified = false;
        clausesRemaining.clear();
        literalToClause.clear();
        set<Clause> cnf_new;
        for (const Clause &c : cnf)
            cnf_new.insert(Clause(c.originalClause));
        cnf.clear();
        auto conflictCNF = implicationGraph->conflictClauses;
        implicationGraph->conflictClauses.clear();
        cnf.clear();
        cnf_new.insert(conflictCNF.begin(), conflictCNF.end());
        for (const auto &c : cnf_new)
            addClause(c);
    }

    /* Returns true if unsat or sat.
     * A function is set to be sat if clausesRemaining.empty is true, that is, if all
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
        if (!literalToClause.count(v))
            return 0;
        return this->literalToClause[v].size();
    }

    /* Applies a solution to a clause (i.e removes potential negated literals). */
    void applySolution(Clause *c) {
        for (auto v : assignedVars) {
            if (count(c->clause.begin(), c->clause.end(), v)) {
                c->clause.clear();
                return;
            }
            c->clause.erase(remove(c->clause.begin(), c->clause.end(), -v), c->clause.end());
            if (c->clause.empty())
                setUnsat(c); // UNSAT!!!!
        }
    }

    void setUnsat(Clause *clause) {
        falsified = true;
        Node *node = implicationGraph->handleConflictClause(clause);
        if (node != nullptr) {
            assertionNode = node;
            assertionHistory.push(assertionNode);
        }
    }

    /* Add a new clause and update information accordingly. */
    void addClause(const Clause &c_) {
        cnf.emplace_back(c_);
        Clause *c = &cnf.back();
        applySolution(c);
        //Re-reference literals.
        for (int v : c->clause) {
            literalToClause[v].push_back(cnf.size() - 1);
            unassignedVars.insert(abs(v));
        }
        if (falsified || !c->clause.empty())
            clausesRemaining.push_back(cnf.size() - 1);
    }

    /* Removes a clause from the unsatisfied list, but updates all parameters accordingly. */
    void discardClause(int index) {
        clausesRemaining.erase(remove(clausesRemaining.begin(), clausesRemaining.end(), index),
                               clausesRemaining.end());
        for (auto v : cnf[index].clause) {
            literalToClause[v].erase(remove(literalToClause[v].begin(),
                                            literalToClause[v].end(), index), literalToClause[v].end());
        }
    }

    /* Adds a literal to the solution list, i.e assigns a ground-truth to a variable. */
    void addSolution(int v, bool implied = false) {
        if (assignedVars.count(v) || falsified)
            return;
        // The counter keeps track on how many assignments we have done.
        COUNTER++;
        if (!implied) {
            Node *node = implicationGraph->addSolutionGuess(v);
            solutionHistory.insert(node);
        }
        unassignedVars.erase(abs(v));
        assignedVars.insert(v);
        //Remove satisfied clauses.
        vector<int> clauses(literalToClause[v]);
        for (auto i : clauses) {
            clausesRemaining.erase(remove(clausesRemaining.begin(), clausesRemaining.end(), i),
                                   clausesRemaining.end());
            for (int v2 : cnf[i].clause)
                literalToClause[v2].erase(remove(literalToClause[v2].begin(),
                                                 literalToClause[v2].end(), i),
                                          literalToClause[v2].end());
        }
        //Remove negated literal from clauses.
        for (auto i : literalToClause[-v]) {
            cnf[i].clause.erase(remove(cnf[i].clause.begin(), cnf[i].clause.end(), -v),
                                cnf[i].clause.end());
            int v2 = cnf[i].clause.front();
            if (cnf[i].clause.size() == 1 && !assignedVars.count(v2)) {
                set<Node *> implications;
                for (auto lit : cnf[i].originalClause) {
                    if (lit != v2)
                        implications.insert(implicationGraph->nodes[-lit]);
                }
                Node *node = implicationGraph->addImplication(v2, implications);
                solutionHistory.insert(node);
                addSolution(v2, true);
            }
        }
        //First clear, then propagate implications.
        for (auto i : literalToClause[-v]) {
            if (cnf[i].clause.empty() && count(clausesRemaining.begin(), clausesRemaining.end(), i)) {
                setUnsat(&cnf[i]); // UNSAT!!!!
                return;
            }
        }
        literalToClause[-v].clear();
        literalToClause[v].clear();
    }

    /* Adds multiple literals to the solution list, i.e assigns ground-truths to variables. */
    void addSolutions(const unordered_set<int> &alpha) {
        for (auto v : alpha)
            addSolution(v);
    }

    /* Performs the resolution rule as stated in the script for a given variable.
     * Assumes the literal and its negation occur both exactly once.
     */
    void resolve(int literal) {
        set<vector<int>> newClauses;
        vector<int> a_;
        for (auto a : literalToClause[literal]) {
            if (!count(cnf[a].clause.begin(), cnf[a].clause.end(), -literal))
                a_.push_back(a);
        }
        int b = literalToClause[-literal][0];
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
            // Since we will be manipulating the original clause, field, add a copy of it to the cnf.
            vector<int> newClause(cnf[a].clause);
            unassignedVars.erase(abs(literal));
            // Merge both clauses.
            newClause.insert(newClause.end(), cnf[b].clause.begin(), cnf[b].clause.end());
            // Delete literals from resolved clause and the original clause.
            newClause.erase(remove(newClause.begin(), newClause.end(), literal), newClause.end());
            newClause.erase(remove(newClause.begin(), newClause.end(), -literal), newClause.end());
            // Remove duplicates.
            sort(newClause.begin(), newClause.end());
            newClause.erase(unique(newClause.begin(), newClause.end()), newClause.end());
            newClauses.insert(newClause);
        }
        // Clear literal(s).
        literalToClause[-literal].clear();
        literalToClause[literal].clear();
        for (const auto &c : newClauses)
            addClause(Clause(c));
    }
};

/* Eliminates clauses that contain both, a variable and its negation, in the same clause. */
void eliminateTautologies(Data *data) {
    vector<int> cnf(data->clausesRemaining);
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

/* Reads a diamacsCNF file from a given path. */
vector<Clause> loadDimacsCnf(const string &path) {
    // cout << "Loading Dimacs-file at \"" << path << "\"." << endl;
    ifstream file(path);
    string str;
    int nLiterals = 0;
    vector<Clause> cnf;
    while (getline(file, str)) {
        if (str[0] != 'c' && str[0] != 'p') {
            vector<int> numbers;
            str = str.substr(0, str.size() - 1);
            stringstream iss(str);
            int number;
            while (iss >> number)
                numbers.push_back(number);
            Clause clause = Clause(numbers);
            cnf.push_back(clause);
            nLiterals += numbers.size();
        }
    }
    // cout << "Done! (Clauses: " << cnf.size() << " | Literals " << nLiterals << ")." << endl;
    return cnf;
}

/* Transforms any CNF to 3-SAT.
 * We do not use this in our version, since the resolution rule sort of "undoes" the procedure. */
vector<vector<int>> to3SAT(const vector<vector<int>> &cnf) {
    cout << "Transforming CNF to 3-SAT..." << endl;
    vector<vector<int>> threeSat;
    int maxVar = 0;
    for (const vector<int> &clause : cnf)
        for (int literal : clause)
            maxVar = max(abs(literal), maxVar);
    for (vector<int> clause : cnf) {
        if (clause.size() <= 3)
            threeSat.push_back(clause);
        else {
            vector<int> v{clause[0], clause[1], ++maxVar};
            threeSat.push_back(v);
            for (int i = 2; i < clause.size() - 2; i++) {
                vector<int> v1{-maxVar, clause[i], ++maxVar};
                threeSat.push_back(v1);
            }
            vector<int> v2{-maxVar, clause[clause.size() - 2], clause[clause.size() - 1]};
            threeSat.push_back(v2);
        }
    }
    cout << "Done! (Clauses old: " << cnf.size() << " | Clauses new: " << threeSat.size() << ")."
         << endl;
    return threeSat;
}

/* Removes clauses that contain only one literal and assigns those as solutions.
 * This also adds edges to the implication graph. */
void removeUnitClauses(Data *data) {
    // cout << "Determining and removing unit clauses and literals." << endl;
    vector<int> cnf(data->clausesRemaining);
    for (auto i : cnf)
        if (data->cnf[i].clause.size() == 1) {
            int literal = data->cnf[i].clause[0];
            data->addSolution(literal);
            if (data->falsified)
                return;
        }
}

/* Determines and removes pure literals from clauses, and respectively includes those as solutions. */
void removePureLiterals(Data *data) {
    // cout << "Detecting and removing pure literals." << endl;
    unordered_set<int> vars(data->unassignedVars);
    //unassignedVars stores only the absolute variable values.
    for (auto v : vars) {
        int a = data->getLiteralCount(v);
        int b = data->getLiteralCount(-v);
        if (b == 0)
            data->addSolution(v);
        else if (a == 0)
            data->addSolution(-v);
        if (data->falsified)
            return;
    }
}

/* Performs the resolution rule, as states in the script (which is similar to combining clauses).
 * Must be called last but before subsumption when used in conjunction with other preprocessing reductions!
 */
void performResolutionRule(Data *data) {
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
                //cout << "\n"<< v;
                //printVector(clause);
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

/* Returns true if there exists a conflict in the solution, i.e same variables is assigned two different ground-truths . */
bool isFalsified(const vector<vector<int>> &cnf, unordered_set<int> alpha) {
    if (alpha.empty())
        return false;
    for (const vector<int> &clause : cnf) {
        for (int v : clause) {
            if (!(alpha.find(v) == alpha.end() && alpha.find(-v) != alpha.end())) {
                return false;
            }
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
    vector<int> cnfUnsat(data->clausesRemaining);
    vector<Clause> cnf(data->cnf);
    for (int i : cnfUnsat)
        sort(cnf[i].clause.begin(), cnf[i].clause.end());
    for (auto largeClause : cnfUnsat) {
        for (auto clause : cnfUnsat) {
            if (cnf[largeClause].clause.size() <= cnf[clause].clause.size())
                continue;
            if (includes(cnf[largeClause].clause.begin(), cnf[largeClause].clause.end(),
                         cnf[clause].clause.begin(), cnf[clause].clause.end())) {
                data->discardClause(largeClause);
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
    return 0;
}

/* Randomly pick a variable! */
int heuristicRandom(Data *data) {
    vector<int> container;
    std::sample(data->unassignedVars.begin(), data->unassignedVars.end(), back_inserter(container),
                1, std::mt19937{std::random_device{}()});
    return container.front();
}

/* Main logic of the sat solver; used for recursion. */
void solveSAT(Data *data) {
    /// PRE-FILTERING:
    if (data->algorithm != Algorithm::Version::NO_PREP) {
        ////////////////////////// REMOVE TAUTOLOGIES ///////////////////////////////
        eliminateTautologies(data);
        ////////////////////////// REMOVE UNIT CLAUSES  ///////////////////////////////
        removeUnitClauses(data);
        if (data->falsified)
            return;
        ////////////////////////// REMOVE PURE LITERALS ///////////////////////////////
        removePureLiterals(data);
        if (data->falsified)
            return;
        ////////////////////////// PERFORM RESOLUTION ///////////////////////////////
        performResolutionRule(data);
        //////////////////////////////////////////////////////////////////////////////
    }
    //////////////////////////  AUTARKIC CLAUSES TRICK  //////////////////////////
    if (data->algorithm != Algorithm::Version::NO_AUT) {
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
    if (!data->unassignedVars.empty()) {
        // Heuristics
        int v;
        if (data->assertionNode == nullptr) {
            if (data->algorithm == Algorithm::Version::HEU_RAND)
                v = heuristicVMTF(data); //heuristicRandom;
            else
                v = heuristicRandom(data); //heuristicVMTF;
            //cout << "(heu=)";
        } else v = -1 * data->assertionNode->literal;
        // Add new guess.
        data->assertionNode = nullptr;
        /*
        if (data.assertionHistory.count(v)) {
            data.unsat = true;
            return data;
        }
         */
        // cout << v << " ";
        data->addSolution(v);
        return;
    }
    data->unsat = data->falsified || !data->clausesRemaining.empty();
}

/* Starts the recursive sat-solver calls and sotres data accordingly in files. */
int solveDimacs(const string &path, Algorithm::Version algorithm) {
    bool sat;
    clock_t tStart = clock();
    srand(unsigned(time(nullptr)));
    cout << "Path: " << path << endl;
    cout << "Algorithm: " << Algorithm::getVersionName(algorithm) << endl;
    vector<Clause> cnf = loadDimacsCnf(path);
    const unordered_set<int> &origVars = getVariables(cnf);
    //cout << "Clauses: " << cnf.size() << " | " << "Vars: " << origVars.size() << endl;
    //cnf = to3SAT(cnf); //Worsens performance!
    ImplicationGraph implicationGraph = ImplicationGraph(cnf);
    Data dataOriginal = Data(&implicationGraph, algorithm);
    Data data(dataOriginal);
    ///////// SAT SOLVER LOOP ////////
    COUNTER = 0;
    eliminateTautologies(&data);
    removePureLiterals(&data);
    removeUnitClauses(&data);
    removeSubsumedClauses(&data);
    performResolutionRule(&data);

    while (!data.canAbort()) {
        solveSAT(&data);
        if (data.falsified)
            data.nonChronologicalBacktracking();
        // Clause deleting strategy
        if (COUNTER % 25000 == 0) {
            auto assignedVars = data.assignedVars;
            data = dataOriginal;
            data.addSolutions(assignedVars);
        }
    }
    ////////////////////////////////
    vector<int> solution;

    if (!data.falsified) {
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
        cout << "SOLVED:\n";
        sort(solution.begin(), solution.end(), [](int x, int y) { return abs(x) < abs(y); });
        printVector(solution);
        cout << "\n";
        sat = true;
    } else {
        cout << "Formula is UNSAT!" << endl;
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

    printf("[Execution time: %.2fs]", (double) (clock() - tStart) / CLOCKS_PER_SEC);
    cout << " [Graph size: " << data.implicationGraph->getSize() << "] " << endl;
    cout << "==========================================================" << endl;
    unordered_set<int> solutionCheck(solution.begin(), solution.end());
    return data.falsified ||
           (verifySolution(cnf, solutionCheck) && removeSatisfiedClauses(cnf, solutionCheck).empty());
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
int main() {
    textFileTimes.open("times.csv");
    textFileSteps.open("steps.csv");
    textFileTimes << "Algorithm";
    textFileSteps << "Algorithm";
    vector<string> paths = getTestFiles("../inputs/test/sat");
    vector<string> paths2 = getTestFiles("../inputs/test/unsat");
    paths.insert(paths.end(), paths2.begin(), paths2.end());
    paths = getTestFiles("../inputs/test/more_complex_tests");
    // paths = {"../inputs/test/more_complex_tests/uf50-014.cnf"};
    // paths = {"../inputs/test/sat/unique.cnf"};
    // paths = {"../inputs/sat/aim-100-1_6-yes1-3.cnf"};
    // paths = {"../inputs/unsat/aim-100-2_0-no-3.cnf"};
    bool correct = true;

    for (int i = 0; i < paths.size(); ++i) {
        textFileTimes << "," << i;
        textFileSteps << "," << i;
    }

    unsigned int stepsTotal = 0;
    for (const auto algorithm : Algorithm::Default) {
        textFileTimes << "\n" << Algorithm::getVersionName(algorithm);
        textFileSteps << "\n" << Algorithm::getVersionName(algorithm);
        for (const auto &path : paths) {
            correct = correct && solveDimacs(path, algorithm);
            stepsTotal += COUNTER;
        }
    }

    textFileTimes.close();
    textFileSteps.close();

    cout << "=> Total steps: " << stepsTotal << ".\n";
    // Here we can double check if our solution is actually true, if not, print it!
    // We can do that by feeding in the solution ot the entire CNF and see if it solves it.
    if (!correct)
        std::cout << "SOMETHING WENT WRONG!";
    else
        std::cout << "SOLUTION CORRECT & CHECKED!";
    return !correct;
}