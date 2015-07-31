import hask


try:
    from setuptools import setup
except ImportError:
    from distutils.core import setup


des = "Haskell language features and standard library ported to Python"
setup(
    name='hask',
    version=hask.__version__,
    description=des,
    long_description=open('README.md').read(),
    author='Bill Murphy',
    author_email='billpmurphy92@gmail.com',
    url='https://github.com/billpmurphy/hask',
    packages=['hask', 'hask.lang', 'hask.Python', 'hask.Data',
              'hask.Control'],
    package_data={'': ['LICENSE', 'README.md']},
    include_package_data=True,
    install_requires=[],
    license=open('LICENSE').read(),
    zip_safe=False,
    classifiers=(
        'Development Status :: 2 - Pre-Alpha',
        'Intended Audience :: Developers',
        'Natural Language :: English',
        'License :: OSI Approved :: BSD License',
        'Programming Language :: Python',
        'Programming Language :: Python :: 2.7'
        ),
)
