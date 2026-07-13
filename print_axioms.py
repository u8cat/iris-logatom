#!/usr/bin/env python3
import re, subprocess, os

ROCQ = "rocq"
FILE = "print_axioms"
PROJECT = '_RocqProject'

flags = []
with open(PROJECT) as f:
    for line in f.readlines():
        if line.startswith('-Q'):
            flags += line.split()

try:
    proc = subprocess.Popen([ROCQ, "compile", FILE+".v"]+flags, stdout=subprocess.PIPE, encoding='utf8')

    axioms = set()
    first_section = True
    for line in proc.stdout:
        line = line.removesuffix('\n')
        if re.fullmatch(r'[ ]+: string', line): continue
        if line == 'Axioms:': continue

        # new section
        m = re.fullmatch(r'"### (.*) ###"', line)
        if m:
            if first_section:
                first_section = False
            else:
                print("")
            print("="*5, m.group(1), "="*5)
            continue

        # new theorem
        m = re.fullmatch(r'"(.*)"', line)
        if m:
            print(f"\nAxioms used by {m.group(1)}:")
            continue

        if line == 'Closed under the global context':
            print('(None)')
        else:
            print(line)
        m = re.match(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)* :", line)
        if m:
            axioms.add(line[m.start():m.end()].removesuffix(" :"))

    axioms = list(axioms)
    axioms.sort()
    print("\n===== Summary =====\n\nList of axioms:")
    for axiom in axioms:
        print(axiom)

    with open(FILE+".txt", 'w') as fd:
        for axiom in axioms:
            print(axiom, file=fd)

finally:
    for suffix in ['glob', 'vo', 'vok', 'vos']:
        os.remove(f'{FILE}.{suffix}')
