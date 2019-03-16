import json
import sys
from z3 import *
import re
from packaging import version

reverse_depends = {}
package_refs = {}

def log(*a):
    pass
    # return print(*a)

class Debug:
    def __repr__(self):
        return str(self.__dict__)

class PackageReference(Debug):
    def __init__(self, ref):
        split = re.split('([<>=]+)', ref)
        name, op, vers = split if len(split) == 3 else [split[0], '', '']
        self.name = name
        self.op = op if op is not '' else None
        self.version = version.parse(vers) if vers else None
        self.ref = Bool(to_encoding(self))

class Constraint(Debug):
    def __init__(self, constraint):
        self.type = 'UNINSTALL' if constraint[0] == '-' else 'INSTALL'
        self.packageref = PackageReference(constraint[1:])

class RepoPackage(Debug):
    def __init__(self, package):
        self.name, self.size = package['name'], int(package['size'])
        self.version = version.parse(package['version'])
        self.depends = [[PackageReference(p) for p in deps] for deps in package['depends']] if 'depends' in package else []
        self.conflicts = [PackageReference(p) for p in package['conflicts']] if 'conflicts' in package else []
        self.ref = Bool(to_encoding(self))
        self.ref0 = Bool(to_encoding(self) + '_init')
        package_refs[to_encoding(self)] = self

class Repository(Debug):
    def __init__(self, repo_packages):
        self.sorted_packages = {}
        self.packages = [RepoPackage(p) for p in repo_packages]
        for package in self.packages:
            if package.name not in self.sorted_packages:
                self.sorted_packages[package.name] = []

            self.sorted_packages[package.name].append((package.version, package.ref, to_encoding(package)))

        for k in self.sorted_packages.keys():
            self.sorted_packages[k] = sorted(self.sorted_packages[k], key=lambda p: p[0])

def to_encoding(package_ref):
    return package_ref.name + '@' + str(package_ref.version)

def nicer(v):
    return v.replace('@', '=')

def find_packages_by_range(package_ref, ret_key=1):
    if package_ref.name not in parsed_repo.sorted_packages:
        return []

    packages = parsed_repo.sorted_packages[package_ref.name]
    if package_ref.op is None:
        return [p[ret_key] for p in packages]

    refs = []

    if package_ref.op is None:
        return refs

    for package in packages:
        if '>' in package_ref.op and package[0] > package_ref.version or \
           '<' in package_ref.op and package[0] < package_ref.version or \
           '=' in package_ref.op and package[0] == package_ref.version:
            refs.append(package[ret_key])

    return refs

def generate_conflicts_s():
    s = []
    for package in parsed_repo.packages:
        conflicts_test = [find_packages_by_range(c) for c in package.conflicts]
        conflicts = [Or(*a) for a in conflicts_test if len(a)]
        if len(conflicts):
            s.append(Implies(package.ref, Not(Or(*conflicts))))

    return And(*s)

def generate_dependencies_s():
    s = []
    for package in parsed_repo.packages:
        deps = []
        for disj in package.depends:
            disjdeps = []
            for conj in disj:
                conjdeps = find_packages_by_range(conj)
                if len(conjdeps):
                    disjdeps.append(Or(*conjdeps))
            if len(disjdeps):
                deps.append(Or(*disjdeps))

        if len(deps):
            s.append(Implies(package.ref, And(*deps)))

    return And(*s)

def generate_repo_s():
    versions = [AtMost(p.ref, 1) for p in parsed_repo.packages]
    no_conflicts_exist = generate_conflicts_s()
    all_dependencies_satisfied = generate_dependencies_s()

    return And(
        *versions,
        no_conflicts_exist,
        all_dependencies_satisfied,
    )

def generate_final_state_s():
    constraints = []
    for constr in constraint_list:
        packages = Or(*find_packages_by_range(constr.packageref))
        if constr.type == 'INSTALL':
            constraints.append(packages)
        else:
            constraints.append(Not(packages))

    return And(*constraints)

def generate_cost_s():
    uninstall = 10**6
    sum_s = []

    for p in parsed_repo.packages:
        sum_s.append(If(And(Not(p.ref0), p.ref), p.size, If(And(p.ref0, Not(p.ref)), uninstall, 0)))

    return Sum(*sum_s)

commands = []
def uninstall(model, i):
    global commands, reverse_depends, initial_packages

    if i not in initial_packages:
        return
    if i in reverse_depends:
        for r in reverse_depends[i]:
            if r in model and not model[r]:
                uninstall(model, r)
    initial_packages.remove(i)
    commands.append('-' + nicer(i))

def install(model, i):
    global commands, package_refs, initial_packages

    if i in initial_packages:
        return
    for disj in package_refs[i].depends:
        for conj in disj:
            for r in find_packages_by_range(conj, ret_key=2):
                if r in model and model[r]:
                    install(model, r)
    initial_packages.append(i)
    commands.append('+' + nicer(i))

if __name__ == '__main__':
    repo = json.load(open(sys.argv[1], "r"))
    initial = json.load(open(sys.argv[2], "r"))
    constraints = json.load(open(sys.argv[3], "r"))

    parsed_repo = Repository(repo)
    initial_state = [PackageReference(i) for i in initial]
    initial_packages = [to_encoding(p) for p in initial_state]
    for package in parsed_repo.packages:
        for disj in package.depends:
            for conj in disj:
                for p in find_packages_by_range(conj, ret_key=2):
                    if p not in reverse_depends:
                        reverse_depends[p] = {}
                    reverse_depends[p][to_encoding(package)] = True

    constraint_list = [Constraint(c) for c in constraints]

    tests = []
    for package in parsed_repo.packages:
        en = to_encoding(package)
        ref = Bool(en + '_init')
        tests.append(And(ref == (en in initial_packages)))

    formula = And(
        generate_repo_s(),
        generate_final_state_s(),
        *tests
    )
    cost = Int('cost')
    cost_formula = generate_cost_s()
    additions = []

    def solve():
        solver = Optimize()
        solver.add(formula)
        solver.add(cost == cost_formula)
        solver.add(*additions)
        solver.minimize(cost)

        timeout_ms = 1 * 30 * 1000
        solver.set('timeout', timeout_ms)
        ck = solver.check()
        if ck != sat:
            return '[]'

        model = solver.model()
        parsed_model = { d.name(): model[d] for d in model if d.name() != 'cost' and '_init' not in d.name()}
        to_remove = [p for p in parsed_model if not parsed_model[p] and p in initial_packages]
        to_install = [p for p in parsed_model if parsed_model[p]]
        for i in to_remove:
            try:
                uninstall(parsed_model, i)
            except:
                additions.append(And(Bool(i) == True))
                return solve()
        for i in to_install:
            try:
                install(parsed_model, i)
            except:
                # cycle, let's give it another try.. unfo, those aren't handled properly
                additions.append(And(Bool(i) == False))
                return solve()

        return json.dumps(commands)

    print(solve())
