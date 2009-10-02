import os, glob, string

ssrdir = os.environ["SSRDIR"]

nodes = ['.']
dirs = []
vs = []
while nodes:
  node = nodes.pop()
  b = os.path.basename(node)
  if (node.endswith('.v')
   and not b.startswith('Opaque_')
   and not b.startswith('Transparent_')):
    vs += [node]
  if os.path.isdir(node) and not b in ['old', 'examples']:
    dirs += [node]
    nodes += glob.glob(node + '/*')

ssr_include = '-I ' + ssrdir + '/theories'
includes = ' '.join(map(lambda x: '-I ' + x, dirs[1:] + [ssrdir + '/theories']))
rs = '-R . CoRN'

coqc = 'ssrcoq -compile ${str(SOURCE)[:-2]} ' + ssr_include + ' ' + rs

env = DefaultEnvironment(ENV = os.environ)
env.Append(BUILDERS = {'Coq' : Builder(action = coqc, suffix = '.vo', src_suffix = '.v')})

for node in vs: env.Coq(node)

os.system('coqdep ' + ' '.join(vs) + ' ' + includes + ' ' + rs + ' > deps')
ParseDepends('deps')
