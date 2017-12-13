import os, glob, string

# Removing examples directory since we do not need it every time.
dirs_to_compile = ['algebra', 'complex', 'coq_reals', 'fta', 'ftc', 'liouville', 'logic', 'metrics', 'model', 'raster', 'reals', 'tactics', 'transc', 'order', 'metric2', 'stdlib_omissions', 'util', 'classes', 'ode']

nodes = map(lambda x: './' + x, dirs_to_compile)
dirs = []
vs = []

env = DefaultEnvironment(ENV = os.environ, tools=['default', 'Coq'])

while nodes:
  node = nodes.pop()
  b = os.path.basename(node)
  if (node.endswith('.v')
   and not b.startswith('Opaque_')
   and not b.startswith('Transparent_')):
    vs += [File(node)]
  if os.path.isdir(node):
    dirs += [node]
    nodes += glob.glob(node + '/*')

includes = ' '.join(map(lambda x: '-I ' + x, dirs[1:]))
Rs = '-R . CoRN'
coqcmd = 'coqc ${str(SOURCE)[:-2]} ' + Rs

env['COQFLAGS'] = Rs

for node in vs: env.Coq(node, COQCMD=coqcmd)
#mc_vs, mc_vos, mc_globs = env.SConscript(dirs='math-classes/src')

os.system('coqdep ' + ' '.join(map(str, vs)) + ' ' + includes + ' ' + Rs + ' > deps')
ParseDepends('deps')

open('coqidescript', 'w').write('#!/bin/sh\ncoqide ' + Rs + ' $@ \n')
os.chmod('coqidescript', 0755)
#env.CoqDoc(env.Dir('coqdoc'), vs+mc_vs, COQDOCFLAGS='-utf8 --toc -g --no-lib-name --coqlib http://coq.inria.fr/library')

env.CoqDoc(env.Dir('coqdoc'), vs, COQDOCFLAGS='-utf8 --toc -g --no-lib-name --coqlib http://coq.inria.fr/library')

#env.Command('deps.dot', [], 'tools/DepsToDot.hs < deps > $TARGET')
