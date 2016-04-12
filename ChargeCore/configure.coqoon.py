#!/usr/bin/env python
# coding=utf-8

# configure.coqoon.py, a configure script for Coqoon projects
# A component of Coqoon, an integrated development environment for Coq proofs
# Copyright © 2014, 2015, 2016 Alexander Faithfull
#
# This script is free software; its author grants unlimited permission to use,
# copy, modify and/or redistribute it.

# Manipulating this project using Coqoon may cause this file to be overwritten
# without warning: any local changes you may have made will not be preserved.

# Remember to keep this value in sync with CoqBuildScript.scala
_configure_coqoon_version = 24

import io, os, re, sys, shlex, codecs
from argparse import ArgumentParser

try:
    import readline
    readline.set_completer_delims(" \t\n")
    readline.parse_and_bind("tab: complete")
except ImportError:
    pass

parser = ArgumentParser(
    description = """\
Generate a site-specific Makefile to compile this Coqoon project.""")
parser.add_argument(
    "vars",
    metavar = "NAME=VALUE",
    help = "the name and value for a variable specifying the path to an " +
           "external dependency",
    nargs = '*')
parser.add_argument(
    "-v", "--version",
    action = "version",
    version = "%(prog)s v" + str(_configure_coqoon_version))
parser.add_argument(
    "-p", "--prompt",
    action = "store_true",
    dest = "prompt",
    help = "prompt the user to specify values for any missing variables")
parser.add_argument(
    "-f", "--file",
    action = "store",
    default = "Makefile",
    dest = "file",
    help = "override the name of the output Makefile")
parser.add_argument(
    "-s", "--strict",
    action = "store_false",
    dest = "persevere",
    help = "don't generate a Makefile if a dependency couldn't be resolved")
parser.add_argument(
    "-Q", "--require-qualification",
    action = "store_true",
    dest = "require_qualification",
    help = "require that library names be fully qualified (Coq 8.5+ only)")
parser.add_argument(
    "-c", "--no-cache",
    action = "store_false",
    dest = "use_cache",
    help = "don't attempt to extract values for variables from a " +
           "previously-generated Makefile")
parser.add_argument(
    "-z", "--quick",
    action = "store_true",
    dest = "go_fast",
    help = "use the quick compilation process to produce .vio files (Coq " +
           "8.5+ only)")

args = parser.parse_args()

def notice(stream, kind, text):
    stream.write("%s: %s: %s\n" % (parser.prog, kind, text))

def info(info):
    notice(sys.stdout, "information", info)

def warn(warning):
    notice(sys.stderr, "warning", warning)

def err(error, usage = True):
    prog = parser.prog
    notice(sys.stderr, "error", error)
    if usage:
        sys.stderr.write("Try \"%s --help\" for more information.\n" % prog)
    sys.exit(1)

def striplist(l):
    return map(lambda s: s.rstrip("/"), l)

# This utility class is modelled loosely upon org.eclipse.core.runtime.Path,
# although is nowhere near as complicated
class Path:
    def __init__(self, i = None):
        if i != None:
            self._bits = striplist(i.split("/"))
        else:
            self._bits = []

    def bit(self, i):
        return self._bits[i]
    def head(self):
        return self._bits[0]
    def tail(self):
        return self.drop_first(1)

    def first(self):
        return self.head()
    def last(self):
        return self._bits[len(self) - 1]

    def drop_first(self, i):
        p = Path()
        p._bits.extend(self._bits[i:])
        return p
    def drop_last(self, i):
        p = Path()
        p._bits.extend(self._bits[:i])
        return p

    def replace(self, i, s):
        p = Path()
        p._bits.extend(self._bits)
        p._bits[i] = s.rstrip("/")
        return p

    def __len__(self):
        return len(self._bits)

    def append(self, i):
        if len(i) != 0:
            p = Path()
            p._bits.extend(self._bits)
            p._bits.append(i.rstrip("/"))
            return p
        else:
            return self
    def append_path(self, i):
        if len(i._bits) != 0:
            p = Path()
            p._bits.extend(self._bits)
            p._bits.extend(i._bits)
            return p
        else:
            return self

    def isdir(self):
        return os.path.isdir(str(self))
    def isfile(self):
        return os.path.isfile(str(self))

    # Convenience file operations
    def open(self, mode = "r", encoding = "utf_8"):
        return io.open(str(self), mode = mode, encoding = encoding)
    def utime(self, times):
        os.utime(str(self), times)

    def __iter__(self):
        return self._bits.__iter__()

    def __str__(self):
        return "/".join(self)

    @staticmethod
    def cwd():
        return Path(os.getcwd())

variables = {} # Variable name -> user-specified value for variable

# Pre-populate the variable store using the command-line arguments
for i in args.vars:
    match = re.match("^(.+)=(.*)$", i, 0)
    if match:
        (var, value) = match.groups()
        variables[var] = value
    else:
        err("don't know what to do with argument \"%s\"" % i)

def examine_makefile(file):
    _vars = {}
    with io.open(args.file, mode = "r", encoding = "utf_8") as file:
        valid = False
        reading_vars = False
        for line in file:
            if not valid:
                if "Generated by configure.coqoon" in line:
                    valid = True
                    if not args.use_cache:
                        break
                else:
                    break
            elif "the following variables were set" in line:
                reading_vars = True
            elif reading_vars:
                match = re.match("^# (.+)=(.*)$", line, 0)
                if match:
                    (var, value) = match.groups()
                    _vars[var] = value
                else:
                    break
        return (valid, _vars)

# If there's already a Makefile in this folder, then we need to tread
# carefully. If we didn't generate it, then we mustn't overwrite it -- but, if
# we did, then we might be able to get some variables out of it
if os.path.isfile(args.file):
    (valid, vs) = examine_makefile(args.file)
    if not valid:
        err("""\
the output file already exists and was not generated by this script, \
aborting""")
    else:
        for vn, val in vs.iteritems():
            if not vn in variables:
                info(("using cached value \"%s\" " +
                      "for variable %s") % (val, vn))
                variables[vn] = val

def prompt_for(vn, prompt, default = None, checker = None):
    if vn in variables:
        return variables[vn]
    elif not args.prompt:
        return default
    print prompt
    try:
        pn = None
        if default == None:
            pn = "%s: " % vn
        else:
            pn = "%s [%s]: " % (vn, default)
        val = raw_input(pn)
        if len(val) > 0:
            if checker == None:
                return val
            else:
                status = checker(val)
                if status == None:
                    return val
                else:
                    warn(status)
                    return prompt_for(vn, prompt, default, checker)
    except EOFError:
        pass
    return default

doomed = False

def coqproject_is_variable(line):
    return line.startswith("COQOON_") or line.startswith("KOPITIAM_")
def coqproject_unpack_variable(line):
    return shlex.split(shlex.split(line)[2])

def load_coq_project_configuration(cwd):
    configuration = []
    # When cwd is none, all the relative paths in @configuration will remain
    # relative; note that this is only ever tolerable for paths known to be
    # within this project
    if cwd == None:
        cwd = Path(None)
    default_output = str(cwd.append("bin"))
    c = None
    try:
        with cwd.append(".coqoonProject").open() as file:
            c = map(shlex.split, file)
    except IOError:
        try:
            with cwd.append("_CoqProject").open() as file:
                c = map(coqproject_unpack_variable,
                        filter(coqproject_is_variable, file))
        except IOError:
            pass
    if c != None and len(c) > 0:
        pv = 0
        for lp in c:
            configuration.append(lp)

            # Make the relative paths absolute
            if lp[0] == "SourceLoadPath":
                lp[1] = str(cwd.append(lp[1]))
                if len(lp) > 2:
                    lp[2] = str(cwd.append(lp[2]))
            elif lp[0] == "DefaultOutput":
                lp[1] = str(cwd.append(lp[1]))
                default_output = lp[1]
            elif lp[0] == "ExternalLoadPath":
                if os.path.isdir(lp[1]):
                    pass
                else:
                    elp_name = lp[2] if len(lp) > 2 else "(unknown)"
                    # Deriving the variable name from its position is hardly
                    # ideal, but we don't have much else to go on for external
                    # load paths...
                    lp[1] = prompt_for("EXT_" + str(pv), """\
Specify the path to the \"%s\" library.""" % elp_name, lp[1])
                    if not os.path.isdir(lp[1]):
                        warn("""\
the library "%s" (EXT_%d) could not be found; dependencies on it will not be \
resolved correctly""" % (elp_name, pv))
                        doomed = True
            pv += 1
    else:
        # If there's no project configuration, use Coqoon's default settings
        configuration = [["SourceLoadPath", str(cwd.append("src"))],
                         ["DefaultOutput", str(cwd.append("bin"))],
                         ["AbstractLoadPath",
                          "dk.itu.sdg.kopitiam/lp/coq/8.4"]]
    return (default_output, configuration)

# Read this project's configuration
default_output, configuration = load_coq_project_configuration(None)

# This script can only support abstract load paths with some help from Coqoon,
# which produces a "configure.coqoon.vars" file specifying incomplete paths to
# the Coq load path entries that are associated with the abstract load paths
# required by this project

def load_vars(path):
    vs = []
    try:
        tokens = []
        with io.open(path, mode = "r", encoding = "utf_8") as file:
            tokens = shlex.split(file.read(), comments = True)
        while len(tokens) != 0:
            v = None
            if tokens[0] == "var":
                (v, tokens) = (tokens[0:3], tokens[3:])
            elif tokens[0] == "alp":
                if tokens[2] == "name":
                    (v, tokens) = (tokens[0:4], tokens[4:])
                elif (tokens[2] == "include" or
                     tokens[2] == "include-recursive"):
                    (v, tokens) = (tokens[0:5], tokens[5:])
                else:
                    tokens = tokens[1:]
            else:
                # Skip this token in the hope that we'll eventually get back in
                # sync
                tokens = tokens[1:]
            if v != None:
                vs.append(v)
    except IOError:
        pass
    return vs

def structure_vars(vs):
    expected_vars = {} # Variable name -> human-readable description of
                       # variable
    alp_names = {} # Abstract load path ID -> human-readable name
    alp_dirs_with_vars = [] # sequence of (abstract load path ID, directory,
                            # coqdir, recursive)
    for i in vs:
        if i[0] == "var":
            expected_vars[i[1]] = i[2]
        elif i[0] == "alp":
            aid = i[1]
            if i[2] == "name":
                alp_names[aid] = i[3]
            elif i[2] == "include":
                alp_dirs_with_vars.append((aid, i[3], i[4], False))
            elif i[2] == "include-recursive":
                alp_dirs_with_vars.append((aid, i[3], i[4], True))
    return (expected_vars, alp_names, alp_dirs_with_vars)

vs = load_vars("configure.coqoon.vars")
if len(vs) == 0:
    warn("""\
the "configure.coqoon.vars" file is missing, empty, or unreadable; \
non-trivial dependency resolution may fail""")

def substitute_variables(expected_vars, alp_names, alp_dirs_with_vars):
    for vn in expected_vars:
        val = prompt_for(vn, "Specify a value for \"%s\"." % expected_vars[vn])
        if val != None:
            variables[vn] = val

        if not vn in variables:
            affected_alps = []
            for aid, directory, _, _ in alp_dirs_with_vars:
                name = "\"%s\"" % alp_names.get(aid, aid)
                if ("$(%s)" % vn) in directory and not name in affected_alps:
                    affected_alps.append(name)
            aalps = None
            if len(affected_alps) == 1:
                aalps = affected_alps[0]
            elif len(affected_alps) > 1:
                aalps = ", ".join(affected_alps[0:-1]) + " and " + affected_alps[-1]
            warn("""\
the variable %s is not defined; dependencies on %s will not be resolved \
correctly""" % (vn, aalps))
    alp_dirs = {} # Abstract load path ID -> sequence of (possibly resolved
                  # directory, coqdir, recursive)
    for aid, directory, coqdir, recursive in alp_dirs_with_vars:
        for vn, vv in variables.items():
            directory = directory.replace("$(%s)" % vn, vv)
        alp_elements = alp_dirs.get(aid, [])
        alp_elements.append((directory, coqdir, recursive))
        alp_dirs[aid] = alp_elements
    return alp_dirs

alp_directories = substitute_variables(*structure_vars(vs))

# Find all source directories and their corresponding output directories
source_directories = [] # sequence of (source directory, output directory)
for i in configuration:
    if i[0] == "SourceLoadPath":
        entry = (i[1], i[2] if len(i) > 2 else default_output)
        source_directories.append(entry)

# Keep this in sync with CoqSentence.getNextSentence
class SentenceIterator:
    # The leading ^ has been removed from all of these regular expressions
    # because RegexObject.match only matches on it when the optional pos
    # argument is missing or zero, and we use that argument to avoid slicing
    # and thus to improve performance
    CommentStart = re.compile(r"\(\*")
    CommentEnd = re.compile(r"\*\)")
    QuotationMark = re.compile("\"")
    Bullet = re.compile(r"(\++|-+|\*+)")
    CurlyBracket = re.compile(r"(\{|\})(\s|$)")
    FullStop = re.compile(r"\.(\s|$)")
    # Python has a mysterious constant called "Ellipsis", so let's not clash
    # with that
    Ellipsis_ = re.compile(r"\.\.\.(\s|$)")

    DotRun = re.compile(r"(\.+)(\s|$)")
    WhitespaceRun = re.compile(r"(\s+)")

    def __init__(self, doc):
        self.doc = doc
        self.offset = 0
    def __iter__(self):
        return self
    # Coqoon considers a Coq command to be a (content as string, comment as
    # boolean) pair. Standalone comments are returned as separate commands
    def next(self):
        i = self.offset
        commentDepth = 0
        inString = False
        content = False

        cd = self.doc
        dl = len(cd) # (total) document length
        while i < dl:
            if SentenceIterator.CommentStart.match(cd, i) \
                    and not inString:
                commentDepth += 1
                i += 2
            elif SentenceIterator.CommentEnd.match(cd, i) \
                    and not content and not inString and commentDepth == 1:
                try:
                    return (self.doc[self.offset:i + 2], True)
                finally:
                    self.offset = i + 2
            elif SentenceIterator.CommentEnd.match(cd, i) \
                    and not inString and commentDepth > 0:
                commentDepth -= 1
                i += 2
            elif SentenceIterator.QuotationMark.match(cd, i):
                inString = not inString
                i += 1
            elif SentenceIterator.FullStop.match(cd, i) \
                    and not inString and commentDepth == 0:
                try:
                    return (self.doc[self.offset:i + 1], False)
                finally:
                    self.offset = i + 1
            elif SentenceIterator.Ellipsis_.match(cd, i) \
                    and not inString and commentDepth == 0:
                try:
                    return (self.doc[self.offset:i + 3], False)
                finally:
                    self.offset = i + 3
            elif SentenceIterator.CurlyBracket.match(cd, i) \
                    and not inString and commentDepth == 0:
                try:
                    return (self.doc[self.offset:i + 1], False)
                finally:
                    self.offset = i + 1
            elif SentenceIterator.Bullet.match(cd, i) \
                    and not content and not inString and commentDepth == 0:
                b = SentenceIterator.Bullet.match(cd, i).group(1)
                try:
                    return (self.doc[self.offset:i + len(b)], False)
                finally:
                    self.offset = i + len(b)
            elif SentenceIterator.DotRun.match(cd, i) \
                    and not inString and commentDepth == 0:
                content = True
                (dots, end) = SentenceIterator.DotRun.match(cd, i).group(1, 2)
                i += len(dots) + len(end)
            elif SentenceIterator.WhitespaceRun.match(cd, i):
                ws = SentenceIterator.WhitespaceRun.match(cd, i).group(1)
                i += len(ws)
            else:
                if commentDepth == 0:
                    content = True
                i += 1
        raise StopIteration

Require = re.compile(
    r"(?s)^\s*Require\s+(Import\s+|Export\s+|)(.*)\s*\.$",
    re.DOTALL + re.MULTILINE)
FromRequire = re.compile(
    r"(?s)^\s*From\s+(.*)\s+Require\s+(Import\s+|Export\s+|)(.*)\s*\.$",
    re.DOTALL + re.MULTILINE)

def extract_dependency_identifiers(f):
    identifiers = []
    for (sentence, is_comment) in SentenceIterator(f.read()):
        if is_comment:
            continue
        match = Require.search(sentence)
        if match != None:
            ids = match.group(2)
            # Using shlex.split here is /technically/ cheating, but it means we
            # can handle both quoted identifiers and multiple identifiers with
            # the same code
            identifiers.extend(shlex.split(ids))
            continue
        match = FromRequire.search(sentence)
        if match != None:
            # We ignore the prefix for the time being, just like Coqoon does
            ids = match.group(3)
            identifiers.extend(shlex.split(ids))
            continue
    return identifiers

def is_name_valid(name):
    # Keep this in sync with CoqCompiler.scala
    for c in name:
        if c.isspace() or c == '.':
            return False
    return True

# Populate the dependency map with the basics: objects depend on sources
deps = {} # Target path -> sequence of dependency paths
to_be_resolved = {}
for srcdir, bindir in source_directories:
    srcroot = Path(srcdir)
    binroot = Path(bindir)
    for current, dirs, files in os.walk(srcdir):
        curbase = os.path.basename(current)
        if not is_name_valid(curbase):
            continue
        srcpath = Path(current)
        binpath = binroot.append_path(srcpath.drop_first(len(srcroot)))
        if not binpath.isdir():
            # Although the Makefile will be able to create this folder, the
            # load path expansion code needs it to exist in order to work
            # properly -- so, like Coqoon, we create it in advance
            os.makedirs(str(binpath))
        for sf_ in filter(lambda f: f.endswith(".v"), files):
            sf = srcpath.append(sf_)
            bf = binpath.append(sf_ + ("o" if not args.go_fast else "io"))
            deps[str(bf)] = [str(sf)]

            # While we're here, stash away the identifiers of the dependencies
            # of this source file
            ids = None
            with sf.open() as file:
                ids = extract_dependency_identifiers(file)
            to_be_resolved[(str(sf), str(bf))] = ids

if not deps:
    err("no source files were found, aborting")

def check_is_project(directory):
    if Path(directory).append(".project").isfile():
        return None
    else:
        return """\
the directory "%s" does not contain a Coqoon project""" % directory

def resolve_load_path(alp_dirs, configuration):
    # This method produces two sequences of (coqdir, resolved directory) pairs:
    # the first is not expanded, but the second is. (The second is used to
    # resolve unqualified or partially-qualified names, and so will only be
    # non-empty if we're not enforcing fully-qualified names.)
    unexpanded_load_path = []
    def expand_pair(coqdir, directory):
        if not os.path.isdir(directory):
            warn("couldn't find directory \"%s\"" % directory)
            return []
        unexpanded_load_path.append((coqdir, directory))
        if args.require_qualification:
            return [] # We don't actually need to do any expansion
        expansion = []
        base = Path(directory)
        for current, _, _ in os.walk(directory):
            curbase = os.path.basename(current)
            if not is_name_valid(curbase):
                continue
            relative = Path(current).drop_first(len(base))
            sub = ".".join(relative)
            full = None
            if len(coqdir) == 0:
                full = sub
            elif len(sub) == 0:
                full = coqdir
            else:
                full = "%s.%s" % (coqdir, sub)
            expansion.append((full, current))
        return expansion
    expanded_load_path = []
    for i in configuration:
        if i[0] == "SourceLoadPath":
            s, b = (i[1], i[2] if len(i) > 2 else default_output)
            expanded_load_path.extend(expand_pair("", s))
            expanded_load_path.extend(expand_pair("", b))
        elif i[0] == "DefaultOutput":
            expanded_load_path.extend(expand_pair("", i[1]))
        elif i[0] == "ExternalLoadPath":
            directory = i[1]
            coqdir = i[2] if len(i) > 2 else ""
            expanded_load_path.extend(expand_pair(coqdir, directory))
        elif i[0] == "AbstractLoadPath":
            alp_elements = alp_dirs.get(i[1])
            if alp_elements != None:
                # We should care about the third entry (recursive descent) in
                # these tuples, but as of Coq 8.5, we seem not to have a
                # choice...
                for d, cd, _ in alp_elements:
                    if not os.path.isdir(d):
                        # Unresolved directory; skip it
                        warn("couldn't find directory \"%s\"" % d)
                        continue
                    else:
                        expanded_load_path.extend(expand_pair(cd, d))
        elif i[0] == "ProjectLoadPath":
            pn = i[1]
            pn_var = "%s_PROJECT_PATH" % pn.upper()

            path = None
            if pn_var in variables:
                path = Path(variables[pn_var])
            elif "WORKSPACE" in variables:
                path = Path(variables["WORKSPACE"]).append(pn)

            if path == None or not path.isdir() \
                            or not path.append(".project").isfile():
                val = prompt_for(pn_var, \
                    "Specify the path to the \"%s\" project." % pn, path,
                    check_is_project)
                if val != None:
                    variables[pn_var] = val
                    path = Path(val)

            if path != None and path.isdir():
                _, cfg = load_coq_project_configuration(path)
                ads = substitute_variables(*structure_vars(load_vars(str(path.append("configure.coqoon.vars")))))
                ulp, elp = resolve_load_path(ads, cfg)
                unexpanded_load_path.extend(ulp)
                expanded_load_path.extend(elp)
            else:
                warning = """\
the project "%s" could not be found; dependencies on it will not be resolved \
correctly""" % pn
                if path == None:
                    warning += """ \
(either specify its path with the %s variable or specify the path to its \
parent directory with the WORKSPACE variable)""" % (pn_var)
                warn(warning)
    return (unexpanded_load_path, expanded_load_path)

unexpanded_load_path, complete_load_path = \
    resolve_load_path(alp_directories, configuration)

# Now that we know the names of all the .vo files we're going to create, we
# can use those -- along with the Coq load path -- to calculate the rest of the
# dependencies
for (sf, bf), identifiers in to_be_resolved.iteritems():
    for ident in identifiers:
        (libdir, _, libname) = ident.rpartition(".")

        # If we require fully-qualified names, then only check the load path's
        # top-level directories; otherwise, check all of them
        lp = unexpanded_load_path if args.require_qualification \
            else complete_load_path

        for coqdir, location in lp:
            # If we're looking for (say) "Coq.ZArith.ZArith", and this folder
            # corresponds to "Coq", then drop the first part and look for
            # "ZArith/ZArith.vo"
            adjusted = libdir if not libdir.startswith(coqdir) \
                else libdir[len(coqdir):]

            p = Path(location)
            for i in adjusted.split("."):
                p = p.append(i)
            result = None
            for c in [ p.append(libname + ".vo"), p.append(libname + ".vio") ]:
                try:
                    os.stat(str(c))
                    result = c
                except:
                    if str(c) in deps:
                        result = c
                if result:
                    break
            if result:
                deps[bf].append(str(result))
                break
        else:
            warn("%s: couldn't resolve dependency \"%s\"" % (str(sf), ident))
            doomed = True

if doomed:
    if not args.persevere:
        err("""\
strict dependency resolution failed, aborting""")
    else:
        warn("""\
dependency resolution failed, but continuing anyway""")

try:
    from socket import gethostname
    from email.Utils import formatdate
    with io.open(args.file, mode = "w", encoding = "utf_8") as file:
        file.write(u"""\
# Generated by configure.coqoon v%d on "%s"
# at %s.
#
# This Makefile was automatically generated; any local changes you may make
# will not be preserved when it is next regenerated.

""" % (_configure_coqoon_version, gethostname(), formatdate(localtime = True)))

        # Dump all the variables provided by the user
        if variables:
            file.write(u"""\
# When this Makefile was generated, the following variables were set:
""")
            for vn, val in variables.iteritems():
                file.write(u"""# %s=%s
""" % (vn, val))
            file.write(u"\n")

        file.write(u"""\
COQC = coqc
COQFLAGS = -noglob
override _COQCMD = \\
	mkdir -p "`dirname "$@"`" && $(COQC) $(COQFLAGS) "$<" && mv "$<%s" "$@"

""" % ("o" if not args.go_fast else "io"))

        output_so_far = []
        for coqdir, location in unexpanded_load_path:
            # There's no sense in generating the same flags over and over
            # again! (In particular, most projects will depend on the Coq
            # standard library, and we don't want to have multiple copies of
            # /that/ mass of flags...)
            if not (coqdir, location) in output_so_far:
                output_so_far.append((coqdir, location))
                if not args.require_qualification:
                    file.write(u"""\
override COQFLAGS += -R "%s" "%s"
""" % (location, coqdir))
                else:
                    file.write(u"""\
override COQFLAGS += -Q "%s" "%s"
""" % (location, coqdir))
        if args.go_fast:
          file.write(u"""\
override COQFLAGS += -quick
""")
        for srcdir, bindir in source_directories:
            object_extension = "vo" if not args.go_fast else "vio"
            file.write(u"""\
%s/%%.%s: %s/%%.v
	$(_COQCMD)

""" % (bindir, object_extension, srcdir))

        file.write(u"""\
OBJECTS = \\
	%s

all: $(OBJECTS)
clean:
	rm -f $(OBJECTS)

""" % " \\\n\t".join([b for b, _ in deps.iteritems()]))

        for f, d in deps.iteritems():
            file.write(u"%s: %s\n" % (f, " ".join(d)))
except IOError as e:
    print e
    pass
