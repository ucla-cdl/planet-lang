from setuptools import setup, find_packages

requirements=[
    "bitarray==2.9.3",
    "bitstring==4.2.3",
    "contourpy==1.3.1",
    "cycler==0.12.1",
    "duckdb==1.1.3",
    "fonttools==4.55.3",
    "Jinja2==3.1.6",
    "kiwisolver==1.4.7",
    "lark==1.2.2",
    "MarkupSafe==3.0.2",
    "matplotlib==3.10.0",
    "numpy==2.1.2",
    "packaging==24.2",
    "pandas==2.2.3",
    "pillow==11.0.0",
    "pyparsing==3.2.0",
    "python-dateutil==2.9.0.post0",
    "pytz==2025.2",
    "six==1.17.0",
    "tzdata==2025.2",
    "z3-solver==4.13.3.0",
]

setup(
    name='planet-dsl',
    version='0.1.4',
    package_dir={"": "src"},
    packages=find_packages(where="src"),
    author='London Bielicke',
    description='A DSL for defining experimental designs',
    install_requires = requirements
)

