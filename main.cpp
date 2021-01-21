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
int COUNTER = 0;
// const auto MAX_THREADS = thread::hardware_concurrency();

/* Namespace to define variations of algorithms that bundles names as access points */
namespace Algorithm {
    enum Version {
        DEFAULT, HEU_LIT, NO_PREP
    };
    // All: Contains all variants
    static const Version All[] = {DEFAULT, HEU_LIT};
    // Contains only the default variant
    static const Version Default[] = {DEFAULT};

    // Return a more informative string if needed.
    string getVersionName(enum Version algorithm) {
        switch (algorithm) {
            case DEFAULT:
                return "Heuristic Variables";
            case HEU_LIT:
                return "Heuristic Literals";
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

/*
 * Implication graph.
 * Here we define the data structure (and its respective operations) for the implication graph.
 * Each Node stores an edge list of implications.
 */
struct ImplicationGraph {
    struct Node {
        unsigned int level;
        vector<int> edges = {};

        explicit Node(unsigned int level) { this->level = level; }
    };

    unsigned int level_index = 0;
    unordered_map<int, Node *> nodes;
    vector<vector<int>> original_cnf;
    vector<vector<int>> conflict_clauses = {};

    explicit ImplicationGraph(vector<vector<int>> original_cnf) { this->original_cnf = std::move(original_cnf); }

    int getSize() const { return nodes.size(); }

    void addSolutionGuess(int literal) {
        nodes[literal] = new Node(++level_index);
    }

    void addImplication(int literal, const vector<int> &implication) {
        nodes[literal] = new Node(level_index);
        // Makes sure the literal itself is not contained in the implication.
        for (auto i : implication) {
            if (i != literal)
                nodes[literal]->edges.push_back(i);
        }
    }

    void handleWrongGuess(int v) {

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
    vector<vector<int>> cnf;
    ImplicationGraph *implicationGraph;
    vector<int> clausesRemaining;
    unordered_set<int> assignedVars;
    unordered_set<int> unassignedVars;
    stack<vector<int>> resolutions;
    unordered_map<int, vector<int>> literalToClause;
    bool unsat = false;
    Algorithm::Version algorithm;

    /* Constructor for the data structure. */
    explicit Data(const vector<vector<int>> &cnf, ImplicationGraph *implicationGraph, Algorithm::Version algorithm) {
        this->implicationGraph = implicationGraph;
        this->cnf = cnf;
        this->algorithm = algorithm;
        for (int i = 0; i < cnf.size(); ++i) {
            clausesRemaining.push_back(i);
            for (auto v : cnf[i]) {
                this->unassignedVars.insert(abs(v));
                this->literalToClause[v].push_back(i);
            }
        }
    }

    /* Returns true if unsat or sat.
     * A function is set to be sat if clausesRemaining.empty is true, that is, if all
     * clauses are satisfied */
    bool canAbort() const {
        return unsat || clausesRemaining.empty();
    }

    /* Returns all clauses which are not yet satisfied. */
    vector<vector<int>> getRemainingClauses() {
        vector<vector<int>> temp;
        for (auto i: clausesRemaining)
            temp.push_back(cnf[i]);
        return temp;
    }

    /* Return the number of times a given literal occurs in unsatisfied clauses. */
    int getLiteralCount(int v) {
        return this->literalToClause[v].size();
    }

    /* Removes a clause from the unsatisfied list, but updaes all parameters accordingly. */
    void discardClause(int index) {
        clausesRemaining.erase(remove(clausesRemaining.begin(), clausesRemaining.end(), index),
                               clausesRemaining.end());
        for (auto v : cnf[index]) {
            literalToClause[v].erase(remove(literalToClause[v].begin(),
                                            literalToClause[v].end(), index), literalToClause[v].end());

        }
    }

    /* Adds a literal to the solution list, i.e assigns a ground-truth to a variable. */
    void addSolution(int v, bool implied = false) {
        unassignedVars.erase(abs(v));
        assignedVars.insert(v);
        //Remove satisfied clauses.
        vector<int> clauses(literalToClause[v]);
        for (auto i : clauses) {
            clausesRemaining.erase(remove(clausesRemaining.begin(), clausesRemaining.end(), i),
                                   clausesRemaining.end());
            for (int v2 : cnf[i])
                literalToClause[v2].erase(remove(literalToClause[v2].begin(),
                                                 literalToClause[v2].end(), i),
                                          literalToClause[v2].end());
        }
        //Remove negated literal from clauses.
        for (auto i : literalToClause[-v]) {
            cnf[i].erase(remove(cnf[i].begin(), cnf[i].end(), -v), cnf[i].end());
            if (cnf[i].empty())
                this->unsat = true; // UNSAT!!!!
        }
        literalToClause[-v].clear();
        literalToClause[v].clear();

        /////////// Update implication graph ///////////
        if (!unsat && !implied)
            implicationGraph->addSolutionGuess(v);
        else if (unsat)
            implicationGraph->handleWrongGuess(v);
        ////////////////////////////////////////////////
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
        int a = literalToClause[literal][0];
        int b = literalToClause[-literal][0];
        // Check if equal.
        if (a == b) {
            addSolution(abs(literal));
            return;
        }
        unassignedVars.erase(abs(literal));
        // Merge both clauses.
        cnf[a].insert(cnf[a].end(), cnf[b].begin(), cnf[b].end());
        // Discard one of them.
        discardClause(b);
        //Re-reference literals.
        for (int v : cnf[b]) {
            if (!count(literalToClause[v].begin(), literalToClause[v].end(), a))
                literalToClause[v].push_back(a);
        }
        // Put the negated literal at the end of the vector (so we can access it easier later on).
        cnf[b].erase(remove(cnf[b].begin(), cnf[b].end(), -literal), cnf[b].end());
        cnf[b].push_back(-literal);
        // Add to the resolution history.
        resolutions.push(cnf[b]);
        // Delete literals from resolved clause.
        cnf[a].erase(remove(cnf[a].begin(), cnf[a].end(), literal), cnf[a].end());
        cnf[a].erase(remove(cnf[a].begin(), cnf[a].end(), -literal), cnf[a].end());
        // Clear literal(s).
        literalToClause[-literal].clear();
        literalToClause[literal].clear();
        // Remove duplicates.
        sort(cnf[a].begin(), cnf[a].end());
        cnf[a].erase(unique(cnf[a].begin(), cnf[a].end()), cnf[a].end());
    }
};

/* Eliminates clauses that contain both, a variable and its negation, in the same clause. */
void eliminateTautologies(Data *data) {
    vector<int> cnf(data->clausesRemaining);
    for (auto i : cnf) {
        for (auto c : data->cnf[i]) {
            if (find(data->cnf[i].begin(), data->cnf[i].end(), -c) != data->cnf[i].end()) {
                //If we have a tautology we can ignore the clause,
                // but do not assign any new variable to the solution!
                data->discardClause(i);
                break;
            }
        }
    }
}

/* Reads a diamacsCNF file from a given path. */
vector<vector<int>> loadDimacsCnf(const string &path) {
    // cout << "Loading Dimacs-file at \"" << path << "\"." << endl;
    ifstream file(path);
    string str;
    int nLiterals = 0;
    vector<vector<int>> cnf;
    while (getline(file, str)) {
        if (str[0] != 'c' && str[0] != 'p') {
            vector<int> numbers;
            str = str.substr(0, str.size() - 1);
            stringstream iss(str);
            int number;
            while (iss >> number)
                numbers.push_back(number);
            cnf.push_back(numbers);
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
        if (data->cnf[i].size() == 1) {
            int literal = data->cnf[i][0];
            vector<int> &cnf_orig = data->implicationGraph->original_cnf[i];
            // We must check if the original clause was a unit clause.
            // If so, we do not want to generate implications.
            bool implied = cnf_orig.size() > 1;
            if (implied)
                data->implicationGraph->addImplication(literal, cnf_orig);
            data->addSolution(literal, implied);
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
    }
}

/* Performs the resolution rule, as states in the script (which is similar to combining clauses).
 * Must be called last but before subsumption when used in conjunction with other preprocessing reductions!
 */
void performResolutionRule(Data *data) {
    unordered_set<int> vars(data->unassignedVars);
    for (auto literal : vars) {
        if (data->getLiteralCount(literal) == 1 && data->getLiteralCount(-literal) == 1) {
            data->resolve(literal);
        }
    }
}

/* Checks for autarkic clauses, as stated in the script. */
bool isAutarkic(const vector<vector<int>> &cnf, unordered_set<int> alpha) {
    for (const vector<int> &clause : cnf) {
        bool conflicts = false;
        bool satisfies = false;
        for (int v : clause) {
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

/* Removes clauses which are satisfied by a given assignment (alpha). */
vector<vector<int>>
removeSatisfiedClauses(const vector<vector<int>> &cnf, unordered_set<int> alpha) {
    vector<vector<int>> filteredCnf;
    for (const vector<int> &clause : cnf) {
        bool remove = false;
        for (int v : clause) {
            if (alpha.find(v) != alpha.end()) {
                remove = true;
                break;
            }
        }
        if (!remove)
            filteredCnf.push_back(clause);
    }
    // cout << "Done! (Clauses old: " << cnf.size() << " | Clauses new: " << filteredCnf.size() << ")." << endl;
    return filteredCnf;
}


/* We will use a third check/test to make sure that our solution is correct. Here, we scrutinize
 * whether the intersection of the solution and each clause is non-empty.
 */
bool verifySolution(const vector<vector<int>> &cnf, const unordered_set<int> &alpha) {
    for (const vector<int> &clause : cnf) {
        bool correct = false;
        for (int v : clause) {
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
vector<int> getSmallestClause(const vector<vector<int>> &cnf) {
    int bestV = -1;
    vector<int> bestK;
    for (const auto &clause : cnf)
        if ((bestV > clause.size() || bestV == -1) && !clause.empty()) {
            bestK = clause;
            bestV = clause.size();
        }
    return bestK;
}

/* Returns a set of all variables in a cnf. */
unordered_set<int> getVariables(const vector<vector<int>> &cnf, bool absolute = false) {
    unordered_set<int> vars;
    for (const auto &clause : cnf)
        for (auto c : clause) {
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
    vector<vector<int>> cnf(data->cnf);
    for (int i : cnfUnsat)
        sort(cnf[i].begin(), cnf[i].end());
    for (auto largeClause : cnfUnsat) {
        for (auto clause : cnfUnsat) {
            if (cnf[largeClause].size() <= cnf[clause].size())
                continue;
            if (includes(cnf[largeClause].begin(), cnf[largeClause].end(),
                         cnf[clause].begin(), cnf[clause].end())) {
                data->discardClause(largeClause);
            }
        }
    }
}

/* Sort unsat clauses, used for heuristics when there exist multiple "smallest" clauses of the same size.
 * Here, the number of variable (not literal) occurrence is of importance!
 * We first need to sort clauses, the the order within the clauses! */
vector<vector<int>> sortUnsatClausesVariables(Data *data, int order = -1) {
    vector<tuple<int, int, int>> cnfOrdered;
    for (int i : data->clausesRemaining) {
        int v = 0;
        int v2 = 0;
        for (auto item : data->cnf[i]) {
            v += data->getLiteralCount(item) + data->getLiteralCount(-item);
            v2 += data->getLiteralCount(item) * data->getLiteralCount(-item);
        }
        v *= order;
        v2 *= order;
        cnfOrdered.emplace_back(v, v2, i);
    }
    sort(cnfOrdered.begin(), cnfOrdered.end());

    vector<vector<int>> cnf;
    for (auto p :cnfOrdered) {
        vector<int> clause = data->cnf[get<2>(p)];
        sort(clause.begin(), clause.end(), [&data](int x, int y) {
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

/* Here, the number of variable (not literal) occurrence is of importance! */
int heuristic_var(Data *data, int order = 1) {
    vector<int> cnf(data->unassignedVars.begin(), data->unassignedVars.end());
    sort(cnf.begin(), cnf.end(), [&data, &order](int x, int y) {
        int a = data->getLiteralCount(x);
        int b = data->getLiteralCount(y);
        int a2 = data->getLiteralCount(-x);
        int b2 = data->getLiteralCount(-y);
        if (a + a2 != b + b2)
            return (a + a2) * order > (b + b2) * order;
        else
            return (a * a2) * order > (b * b2) * order;
    });
    return cnf.front();
}

/* Here, the number of literal (not variable) occurrence is of importance! */
int heuristic_lit(Data *data, int order = 1) {
    vector<int> cnf(data->unassignedVars.begin(), data->unassignedVars.end());
    sort(cnf.begin(), cnf.end(), [&data, &order](int x, int y) {
        int a = data->getLiteralCount(x);
        int b = data->getLiteralCount(y);
        int a2 = data->getLiteralCount(-x);
        int b2 = data->getLiteralCount(-y);
        if (a != b)
            return a * order > b * order;
        else
            return (a * a2) * order > (b * b2) * order;
    });
    return cnf.front();
}

/* Main logic of the sat solver; used for recursion. */
Data solveSAT(Data data) {
    if (data.canAbort())
        return data;
    COUNTER++;
    /// PRE-FILTERING:
    ////////////////////////// REMOVE PURE LITERALS ///////////////////////////////
    eliminateTautologies(&data);
    ////////////////////////// REMOVE PURE LITERALS ///////////////////////////////
    removePureLiterals(&data);
    ////////////////////////// PERFORM RESOLUTION RULE ////////////////////////////
    performResolutionRule(&data);
    ////////////////////////// REMOVE SUBSUMED THREE CLAUSES //////////////////////
    removeSubsumedClauses(&data);
    ////////////////////////// REMOVE UNIT CLAUSES ///////////////////////////////
    /* Must be last as we determine here conflict clauses! */
    removeUnitClauses(&data);
    //////////////////////////////////////////////////////////////////////////////

    if (data.canAbort())
        return data;
    vector<vector<int>> cnf;

    //////////////////////////  AUTARKIC CLAUSES TRICK  //////////////////////////
    cnf = sortUnsatClausesVariables(&data);
    vector<int> nextClause = getSmallestClause(cnf);
    vector<unordered_set<int>> ys;
    for (int i = 0; i < nextClause.size(); ++i) {
        unordered_set<int> assignmentNew = {};
        assignmentNew.insert(nextClause[i]);
        for (int j = 0; j < i; ++j)
            assignmentNew.insert(-nextClause[j]);
        if (isAutarkic(cnf, assignmentNew)) {
            data.addSolutions(assignmentNew);
            return solveSAT(data);
        }
        ys.push_back(assignmentNew);
    }
    ////////////////////////// CORE ALGORITHM  //////////////////////////
    if (!data.unassignedVars.empty()) {
        // Heuristics
        int v;
        if (data.algorithm == Algorithm::Version::HEU_LIT)
            v = heuristic_lit(&data);
        else
            v = heuristic_var(&data);
        // Branching
        for (const auto &y : {1, -1}) {
            Data d = data;
            d.addSolution(v * y);
            if (d.unsat)
                continue;
            d = solveSAT(d);
            if (!d.unsat && d.clausesRemaining.empty())
                return d;
        }
    }
    data.unsat = true;
    data.assignedVars.clear();
    return data; // UNSAT
}

/* Starts the recursive sat-solver calls and sotres data accordingly in files. */
int solveDimacs(const string &path, Algorithm::Version algorithm) {
    bool sat;
    clock_t tStart = clock();
    srand(unsigned(time(nullptr)));
    cout << "Path: " << path << endl;
    cout << "Algorithm: " << Algorithm::getVersionName(algorithm) << endl;
    vector<vector<int>> cnf = loadDimacsCnf(path);
    const unordered_set<int> &origVars = getVariables(cnf);
    //cout << "Clauses: " << cnf.size() << " | " << "Vars: " << origVars.size() << endl;
    //cnf = to3SAT(cnf); //Worsens performance!
    ImplicationGraph implicationGraph = ImplicationGraph(cnf);
    Data data = Data(cnf, &implicationGraph, algorithm);
    /////////
    COUNTER = 0;
    data = solveSAT(data);
    ///
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
                if (removeSatisfiedClauses({vec}, alpha).empty())
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
        cout << "SOLVED! Solution is: ";
        sort(solution.begin(), solution.end(), [](int x, int y) { return abs(x) < abs(y); });
        printVector(solution);
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
    cout << "==================================================" << endl;
    unordered_set<int> solutionCheck(solution.begin(), solution.end());
    return data.unsat ||
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
    // paths = getTestFiles("../inputs/test/more_complex_tests");
    // paths = {"../inputs/sat/uf50-08.cnf","../inputs/sat/uf50-09.cnf"};
    // paths = {"../inputs/sat/aim-100-1_6-yes1-3.cnf"};
    // paths = {"../inputs/unsat/aim-100-2_0-no-3.cnf"};
    bool correct = true;

    for (int i = 0; i < paths.size(); ++i) {
        textFileTimes << "," << i;
        textFileSteps << "," << i;
    }

    for (const auto algorithm : Algorithm::Default) {
        textFileTimes << "\n" << Algorithm::getVersionName(algorithm);
        textFileSteps << "\n" << Algorithm::getVersionName(algorithm);
        for (const auto &path : paths)
            correct = correct && solveDimacs(path, algorithm);
    }

    textFileTimes.close();
    textFileSteps.close();
    // Here we can double check if our solution is actually true, if not, print it!
    // We can do that by feeding in the solution ot the entire CNF and see if it solves it.
    if (!correct)
        std::cout << "SOMETHING WENT WRONG!";
    else
        std::cout << "SOLUTION CORRECT & CHECKED!";
    return !correct;
}