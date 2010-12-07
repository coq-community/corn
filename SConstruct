import os, glob, string

ssrdir = os.environ["SSRDIR"]

dirs_to_compile = ['algebra', 'complex', 'coq_reals', 'fta', 'ftc', 'logic', 'metrics', 'model', 'raster', 'reals', 'tactics', 'transc', 'order', 'metric2', 'Liouville', 'examples', 'stdlib_omissions', 'util']

nodes = map(lambda x: './' + x, dirs_to_compile)
dirs = []
vs = []

while nodes:
  node = nodes.pop()
  b = os.path.basename(node)
  if (node.endswith('.v')
   and not b.startswith('Opaque_')
   and not b.startswith('Transparent_')):
    vs += [node]
  if os.path.isdir(node):
    dirs += [node]
    nodes += glob.glob(node + '/*')

ssr_include = '-I ' + ssrdir + '/theories -as Ssreflect'
includes = ' '.join(map(lambda x: '-I ' + x, dirs[1:] + [ssrdir + '/theories']))
Rs = '-R . CoRN -exclude-dir MathClasses -I MathClasses '

coqc = ssrdir + '/bin/ssrcoq -compile ${str(SOURCE)[:-2]} ' + ssr_include + ' ' + Rs

env = DefaultEnvironment(ENV = os.environ)
env.Append(BUILDERS = {'Coq' : Builder(action = coqc, suffix = '.vo', src_suffix = '.v')})

for node in vs:
  vo = env.Coq(node)
  env.Clean(vo, node[:-2] + '.glob')

os.system('coqdep ' + ' '.join(vs) + ' ' + includes + ' ' + Rs + ' > deps')
ParseDepends('deps')

open('coqidescript', 'w').write('#!/bin/sh\n' + ssrdir + '/bin/ssrcoqide ' + ssr_include + ' ' + Rs.replace('"', '\\"') + ' $@ \n')
os.chmod('coqidescript', 0755)
