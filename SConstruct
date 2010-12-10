import os, glob, string

dirs_to_compile = ['algebra', 'complex', 'coq_reals', 'fta', 'ftc', 'logic', 'metrics', 'model', 'raster', 'reals', 'tactics', 'transc', 'order', 'metric2', 'Liouville', 'examples', 'stdlib_omissions', 'util']

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

ssrdir = os.environ["SSRDIR"]
ssrcoq = ssrdir + '/bin/ssrcoq'
ssr_include = '-I ' + ssrdir + '/theories -as Ssreflect'
includes = ' '.join(map(lambda x: '-I ' + x, dirs[1:] + [ssrdir + '/theories']))
Rs = '-R . CoRN'
coqcmd = ssrcoq + ' -compile ${str(SOURCE)[:-2]} ' + ssr_include + ' ' + Rs

env['COQFLAGS'] = Rs

for node in vs: env.Coq(node, COQCMD=coqcmd)

mc_vs, mc_vos, mc_globs = env.SConscript(dirs='MathClasses')

os.system('coqdep ' + ' '.join(map(str, vs+mc_vs)) + ' ' + includes + ' ' + Rs + ' > deps')
ParseDepends('deps')

open('coqidescript', 'w').write('#!/bin/sh\n' + ssrdir + '/bin/ssrcoqide ' + ssr_include + ' ' + Rs.replace('"', '\\"') + ' $@ \n')
os.chmod('coqidescript', 0755)

env.CoqDoc(env.Dir('coqdoc'), vs+mc_vs, COQDOCFLAGS='-utf8 --toc -g --no-lib-name')

env.Command('deps.dot', [], 'tools/DepsToDot.hs < deps > $TARGET')
