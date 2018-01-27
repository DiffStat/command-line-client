#!/usr/bin/env python2.7
#
# Copyright 2018 DiffStat.com. All Rights Reserved.
#
# NOTICE:  All information contained herein is, and remains the property of
# DiffStat.com and its suppliers, if any. The intellectual and technical
# concepts contained herein are proprietary to DiffStat.com and its suppliers
# and may be covered by U.S. and Foreign Patents, patents in process, and are
# protected by trade secret or copyright law. Unauthorized use of this file for
# any operation besides those related to interacting with the DiffStat.com
# website is strictly prohibited.

"""Provides a command-line interface for interacting with DiffStat.com APIs

For detailed documentation, visit:
https://www.diffstat.com/client-documentation
"""


###############################################################################
# Imports

from __future__ import print_function, with_statement

import argparse
import gc
import getpass
import hashlib
import json
import logging
import os
import platform
import re
import shlex
import signal
import subprocess
import sys
import tempfile
import textwrap
import time
import unicodedata
import urllib
import urllib2
import urlparse


################################################################################
# Authorship

__author__ = 'DiffStat.com.'
__copyright__ = 'Copyright 2018, DiffStat.com, All Rights Reserved'
__email__ = 'info@DiffStat.com'
__status__ = 'Production'
__version__ = '1.0.0'


################################################################################
# Constants

SCRIPT_VERSION = '1.0.0'
DEVNULL = open(os.devnull, 'wb')
LOG_LEVEL = logging.INFO
LOG_FORMAT_STREAM = '%(asctime)s - %(levelname)s - %(message)s'
LOG_FORMAT_FILE = ('%(asctime)s - %(name)s - %(funcName)s (%(lineno)d) - '
                   '%(levelname)s - %(message)s')
LOG_DIR = os.environ.get('LOG_DIR', '~/.diffstat')
LOG_FILE = os.environ.get('LOG_FILE', '~/.diffstat/diffstat.log')
CONFIG_FILE = os.environ.get('CONFIG_FILE', '~/.diffstat/config.json')
CONFIG_FILE_COMMENT = ('This is your auto-generated DiffStat.com '
                       'configuration file. Do not modify its contents, '
                       'and do not share your API key with anyone.')

REGISTRATION_NOTICE = """
To access your reports in the DiffStat Web UI, you must register an account.

If you already have a DiffStat account, simply enter your existing DiffStat
login credentials. If you do not already have an account, enter your email
address and your desired password and an account will be created for you.
An account activation link will be sent to the email address you provide.
""".strip()

GIT_LOG_FORMAT = '%x1f'.join([
    '%H', '%P', '%an', '%aN', '%ae', '%aE', '%at', '%aI', '%cn', '%cN',
    '%ce', '%cE', '%ct', '%cI', '%e', '%s', '%b']) + '%x1e'

GIT_COMMIT_FIELDS = [
    'commit_hash', 'parent_hashes', 'author_name', 'author_name_mapped',
    'author_email', 'author_email_mapped', 'author_date', 'author_date_iso',
    'committer_name', 'committer_name_mapped', 'committer_email',
    'committer_email_mapped', 'committer_date', 'committer_date_iso',
    'encoding', 'subject', 'body']

# DiffStat server
SERVER_CHUNK_SIZE = 1000
DIFFSTAT_BASE_URL = os.environ.get('DIFFSTAT_BASE_URL',
                                   'https://www.diffstat.com')
API_KEY_REGISTRATION_URL = DIFFSTAT_BASE_URL + '/v1/api-key-registration'
COMMITS_URL = DIFFSTAT_BASE_URL + '/v1/commits'
REPOSITORIES_URL = DIFFSTAT_BASE_URL + '/v1/repositories'
REPORTS_URL = DIFFSTAT_BASE_URL + '/reports'
SIGNUP_URL = DIFFSTAT_BASE_URL + '/v1/command-line-signup'
SIGNUP_INIT_URL = DIFFSTAT_BASE_URL + '/v1/command-line-signup-init'

# Github
GITHUB_API_URL = 'https://api.github.com'
GITHUB_GRAPHQL_URL = 'https://api.github.com/graphql'
GITHUB_TOKEN_URL = 'https://github.com/settings/tokens'
REQUIRED_OAUTH_SCOPES = [
    {'scope': 'public_repo', 'parent': 'repo'},
    {'scope': 'read:org', 'parent': 'admin:org'},
    {'scope': 'read:user', 'parent': 'user'},
]


################################################################################
# Placeholders

logger = None

# Used to recover a 'git log --numstat' command that runs out of system memory
STAT_PROCESS = None


################################################################################
# Custom Exceptions

class CommitHashNotFoundError(Exception):
    pass


class EmptyRepositoryError(Exception):
    pass


class AmbiguousHeadError(Exception):
    pass


class GitError(Exception):
    pass


class AlarmError(Exception):
    pass


def alarm_handler(signum, frame):
    raise AlarmError


################################################################################
# Utilities

def shell(cmd, env=None):
    if env is None:
        env = dict()
    proc = subprocess.Popen(cmd,
                            env=env,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,
                            shell=True)
    stdout, stderr = proc.communicate()
    return stdout, stderr, proc.returncode


def raise_exception(cmd, stdout, stderr, return_code):
    raise Exception('Error running command: {}\n'
                    'Stdout: {}\n'
                    'Stderr: {}\n'
                    'Exit Code: {}'.format(cmd, stdout, stderr, return_code))


def get_git_version():
    stdout, stderr, retcode = shell('git --version')
    if retcode != 0:
        logger.critical('Git executable not found: %s', stderr)
        sys.exit(1)
    else:
        match = re.search('^git version (.+)$', stdout)
        if match is None:
            logger.critical('Git version not found')
            sys.exit(1)
        else:
            version = match.groups()[0]
            logger.debug('Git version: %s', version)
            return version


def get_file_md5(file_path):
    hash_md5 = hashlib.md5()

    with open(file_path, 'rb') as f:
        for chunk in iter(lambda: f.read(4096), b''):
            hash_md5.update(chunk)

    md5 = hash_md5.hexdigest()
    logger.debug('File MD5: %s', md5)
    return md5


class ChDir(object):
    """Step into a directory temporarily."""
    def __init__(self, path):
        self.old_dir = os.getcwd()
        self.new_dir = path

    def __enter__(self):
        os.chdir(self.new_dir)

    def __exit__(self, *args):
        os.chdir(self.old_dir)


def run_in_dir(dir_, cmd, return_proc=False):
    with ChDir(dir_):
        proc = subprocess.Popen(shlex.split(cmd),
                                stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)
        if return_proc:
            return proc
        else:
            stdout, stderr = proc.communicate()
            return stdout, stderr, proc.returncode


def slugify(git_url):
    # Remove leading and trailing spaces, and convert to lowercase.
    result = git_url.strip().lower()

    # Remove .git suffix
    result = re.sub('\.git$', '', result)

    # Convert to ASCII
    result = unicodedata.normalize('NFKD', unicode(result)).\
        encode('ascii', 'ignore').decode('ascii')
    result = result.replace('/', '-')

    # Remove any char except alphanumeric, spaces, underscore, or hyphen
    result = re.sub(r'[^\w\s_-]', '', result)

    # Remove leading hyphens
    result = result.lstrip('-')

    # Convert sequences of non-alphanumeric characters to a single hyphen
    result = re.sub(r'[\s_-]+', '-', result)

    logger.info('Slugified "%s" to "%s"', git_url, result)
    return result


def send_request(url, data=None, method='GET', headers=None,
                 return_headers=False, include_headers=False):
    if headers is None:
        headers = {}

    if data:
        try:
            data = json.dumps(data)
        except (TypeError, ValueError):
            pass

    request = urllib2.Request(url, data, headers)
    request.get_method = lambda: method

    try:
        reply = urllib2.urlopen(request)
    except urllib2.HTTPError as e:
        e.server_response = e.read()
        parsed_url = urlparse.urlparse(url)
        parsed_diffstat_url = urlparse.urlparse(SIGNUP_URL)

        if parsed_url.netloc == parsed_diffstat_url.netloc and e.code == 401:
            if e.server_response == 'Invalid API Key':
                msg = ('API Authentication failed - Did you accidentally '
                       'modify the DiffStat.com configuration file '
                       '({}) ?'.format(CONFIG_FILE))
                logger.critical(msg)
                sys.exit(1)

        # Error cannot be handled. Just re-raise the exception.
        raise

    res_headers = reply.info()
    if return_headers:
        return res_headers

    content = reply.read()
    reply.close()

    try:
        res_data = json.loads(content)
    except ValueError:
        res_data = content

    if include_headers:
        return (res_headers, res_data)
    else:
        return res_data


def is_commit_hash(s):
    return re.match('^[a-f0-9]{40}$', s)


def init_logger(verbose=False):
    global logger

    if verbose:
        log_level = logging.DEBUG
    else:
        log_level = logging.INFO

    try:
        os.makedirs(os.path.expanduser(LOG_DIR))
    except OSError:
        if not os.path.isdir(os.path.expanduser(LOG_DIR)):
            raise

    logging.basicConfig(filename=os.path.expanduser(LOG_FILE),
                        format=LOG_FORMAT_FILE,
                        level=log_level)
    logger = logging.getLogger(__name__)

    if len(logger.handlers) == 0:
        ch = logging.StreamHandler(sys.stderr)
        ch.setLevel(log_level)
        formatter = logging.Formatter(LOG_FORMAT_STREAM)
        ch.setFormatter(formatter)
        logger.addHandler(ch)

    return logger


def get_github_token():
    token = os.environ.get('DIFFSTAT_GITHUB_TOKEN')

    if token is None or not token.strip():
        logger.critical(textwrap.dedent("""
        Error: The DIFFSTAT_GITHUB_TOKEN environment variable is not set, but it
        needs to be set or specified via the -t/--token flag.

        To create a GitHub token, log in to your GitHub account, and navigate
        to the "Personal access tokens" page under "Settings":

        https://github.com/settings/tokens

        Create a token with the following scopes:

        {}

        On your local machine, set the environment variable to the token's
        value:

        export DIFFSTAT_GITHUB_TOKEN="PASTE_TOKEN_VALUE_HERE"
        """).format('\n'.join([i['scope'] for i in REQUIRED_OAUTH_SCOPES])))
        sys.exit(1)
    else:
        return token


################################################################################
# Git utilities

class Tree(object):
    def __init__(self, relative_root):
        self.relative_root = relative_root
        self.absolute_root = os.path.normpath(os.path.join(os.getcwd(),
                                              self.relative_root))
        # Try to change into the directory. Will raise an exception if the
        # directory does not exist.
        with ChDir(self.absolute_root):
            pass

    def _get_git_dirs(self):
        git_dirs = []
        for (dirpath, dirnames, files) in os.walk(self.absolute_root):
            try:
                with ChDir(dirpath):
                    logger.info('Checking if %s is a git repository', dirpath)
                    subprocess.check_call('git rev-parse', stdout=DEVNULL,
                                          stderr=DEVNULL, shell=True)
                    # No CalledProcessError was raised, so this directory is a
                    # Git repository. Save it and set dirnames to the empty
                    # list to stop further recursive checks - see help(os.walk)
                    # for more info on how this works.
                    logger.info('Git repository found at %s', dirpath)
                    git_dirs.append(dirpath)
                    dirnames[:] = []
            except subprocess.CalledProcessError:
                pass

        return git_dirs

    def sync_all_repositories(self):
        for git_dir in self._get_git_dirs():
            repo = Repo(git_dir)
            client = Client()
            client.send_commits(repo, SERVER_CHUNK_SIZE)


class Clone(object):
    def __init__(self, remote_url, identity_file):
        self.remote_url = remote_url
        self.local_path = slugify(remote_url)
        self.identity_file = identity_file

    def _make_git_ssh(self):
        f = tempfile.NamedTemporaryFile(delete=False)
        f.write('\n'.join((
            '#!/bin/bash',
            '',
            'ssh -o StrictHostKeyChecking=no \\',
            '    -o IdentitiesOnly=yes \\',
            '    -F /dev/null \\',
            '    -i {} "$@"'.format(self.identity_file),
        )))
        f.close()
        os.chmod(f.name, 0o755)
        return f.name

    def _pull(self, env):
        try:
            self._set_tracking_branch()
        except EmptyRepositoryError as e:
            logger.info('Error setting tracking branch: %s', e.message)
            return True
        except AmbiguousHeadError as e:
            logger.info('Error setting tracking branch: %s', e.message)
            return True

        with ChDir(self.local_path):
            logger.info('Git fetching at path: %s', self.local_path)
            _, stderr, retcode = shell('git clean -dxf', env=env)
            if retcode != 0:
                raise GitError('Error calling "git clean" for repo "%s": %s',
                               self.remote_url, stderr)

            _, stderr, retcode = shell('git pull', env=env)
            if retcode != 0:
                if 'does not have any commits yet' in stderr.lower():
                    return True
                raise GitError('Error calling "git pull" for repo "%s": %s',
                               self.remote_url, stderr)
            return True

    def _clone(self, env):
        try:
            cmd = ['git', 'clone', self.remote_url, self.local_path]
            logger.info('Running command: %s', ' '.join(cmd))
            subprocess.check_output(cmd, env=env)
            # Set the tracking branch to be the same as the local branch so
            # that "git pull" can fetch and merge without any arguments.
            self._set_tracking_branch()
            return True
        except EmptyRepositoryError as e:
            logger.info('Error setting tracking branch: %s', e.message)
            return True
        except AmbiguousHeadError as e:
            logger.info('Error setting tracking branch: %s', e.message)
            return True
        except subprocess.CalledProcessError as e:
            logger.info('Error calling "git clone" for repo "%s": %s',
                        self.remote_url, e.message)
            raise

    def _set_tracking_branch(self):
        with ChDir(self.local_path):
            out, err, retcode = shell('git rev-parse --abbrev-ref HEAD')
            if retcode != 0:
                msg = 'No commits in repository: {}'.format(self.local_path)
                raise EmptyRepositoryError(msg)
            elif 'is ambiguous' in (out + err):
                msg = 'HEAD is ambiguous in repository: {}'.format(
                    self.local_path)
                raise AmbiguousHeadError(msg)
            branch = out.strip()
            tracking = ['git', 'branch', '-u', 'origin/{}'.format(branch)]
            subprocess.check_output(tracking)

    def sync(self):
        try:
            if self.identity_file:
                git_ssh = self._make_git_ssh()
                env = {'GIT_SSH': git_ssh}
            else:
                logger.info('No SSH identify file specified. Git will offer '
                            'default private keys located at ~/.ssh/id_rsa '
                            'and ~/.ssh/id_dsa')
                git_ssh = None
                env = {}

            if os.path.exists(self.local_path):
                return self._pull(env)
            else:
                return self._clone(env)
        finally:
            if git_ssh:
                os.remove(git_ssh)


################################################################################
# DiffStat-specific Logic

class Repo(object):
    def __init__(self, repo_path):
        self.repo_path = unicode(repo_path)

    def list_stats(self, start_hash, stop_hash, empty):
        global STAT_PROCESS

        if empty:
            numstat = ''
        else:
            numstat = '--numstat'

        if start_hash is None:
            cmd = ('git log -w --topo-order --format="%x1e%H" {} '
                   '{}'.format(numstat, stop_hash))
        else:
            if not is_commit_hash(start_hash):
                raise Exception('Invalid commit hash: %s' % start_hash)

            cmd = 'git log -w --topo-order --format="%x1e%H" {} ' \
                  '{}..{}'.format(numstat, start_hash, stop_hash)

        proc = run_in_dir(self.repo_path, cmd, return_proc=True)
        # Set a global that can be recovered easily
        STAT_PROCESS = proc
        stat_log, stderr = proc.communicate()
        return_code = proc.returncode
        STAT_PROCESS = None

        if return_code != 0:
            raise_exception(cmd, stat_log, stderr, return_code)

        return stat_log

    def get_origin_url(self):
        stdout, stderr, retcode = shell('git config --get remote.origin.url')
        if retcode != 0:
            return ''
        else:
            url = stdout.strip()
            return url

    def get_name(self):
        """Return the name of the repo to be stored on the server."""
        url = self.get_origin_url()

        if url is None or url.strip() == '':
            logger.debug('No origin set for repository %s', self.repo_path)
            return self.repo_path
        else:
            url = re.sub('\.git$', '', url)
            return url

    def commit_exists(self, hash_):
        with ChDir(self.repo_path):
            p1 = subprocess.Popen(['git', 'log', '--format="%H"'],
                                  stdout=subprocess.PIPE)
            p2 = subprocess.Popen(['grep', hash_], stdin=p1.stdout,
                                  stdout=subprocess.PIPE)
            # Allow p1 to receive a SIGPIPE if p2 exits.
            p1.stdout.close()
            p2.communicate()
            return p2.returncode == 0

    def list_commit_hashes(self):
        #
        # The --first-parent flag is required to avoid commits being sent to the
        # server more than once. Consider the following tree:
        #
        #   .------f---g-----.
        #  /                 \
        # a---b---c----------h---i
        #
        # --> more recent commits -->
        #
        # Without --first-parent:
        # git log a..c => b, c
        # git log c..g => f, g
        # git log g..i => b, c, h, i
        #
        # As you can see, b and c are repeated, which will cause issues when
        # sending these commits to the server.
        #
        # With --first-parent:
        # git log --first-parent a..c => b, c
        # git log --first-parent c..i => f, g, h, i
        #
        cmd = 'git log --first-parent --topo-order --reverse --format="%H"'
        stdout, stderr, return_code = run_in_dir(self.repo_path, cmd)
        if return_code != 0:
            if 'does not have any commits yet' in stderr.lower():
                msg = 'No commits in repository: {}'.format(self.repo_path)
                raise EmptyRepositoryError(msg)
            else:
                raise_exception(cmd, stdout, stderr, return_code)
        hashes = stdout.strip()
        if hashes == '':
            return []
        else:
            return hashes.split('\n')

    def get_commit_indices(self, commit_hashes):
        return {commit_hash: i for i, commit_hash in enumerate(commit_hashes)}

    def compute_stop_hash(self, start_hash, commit_hashes, commit_indices,
                          chunk_size):
        if chunk_size is None:
            chunk_size = SERVER_CHUNK_SIZE
        if start_hash:
            try:
                start_index = commit_indices[start_hash]
                end_index = start_index + chunk_size
                stop_hash = commit_hashes[:end_index + 1][-1]
            except KeyError:
                raise CommitHashNotFoundError
        else:
            end_index = chunk_size
            try:
                stop_hash = commit_hashes[:end_index][-1]
            except IndexError:
                raise EmptyRepositoryError('No commits in this repository')

        return stop_hash

    def list_commits(self, start_hash, stop_hash):
        if start_hash:
            cmd = 'git merge-base {} HEAD'.format(start_hash)
            merge_base, _, return_code = run_in_dir(self.repo_path, cmd)
            if return_code != 0 or merge_base.strip() != start_hash:
                raise CommitHashNotFoundError

        if start_hash is None:
            cmd = ('git log -w --topo-order --reverse --format="{}" '
                   '{}'.format(GIT_LOG_FORMAT, stop_hash))
        else:
            cmd = ('git log -w --topo-order --reverse --format="{}" '
                   '{}..{}'.format(GIT_LOG_FORMAT, start_hash, stop_hash))

        commit_log, stderr, return_code = run_in_dir(self.repo_path, cmd)

        if return_code != 0:
            if 'does not have any commits yet' in stderr:
                return ''
            else:
                raise_exception(cmd, commit_log, stderr, return_code)

        return commit_log

    def get_commit_objects(self, start_hash=None, chunk_size=None,
                           include_diffstat=True):
        # http://blog.lost-theory.org/post/how-to-parse-git-log-output/
        commit_hashes = self.list_commit_hashes()
        commit_indices = self.get_commit_indices(commit_hashes)
        while True:
            logger.debug('Computing stop hash from %s with chunk size %s',
                         start_hash, chunk_size)
            stop_hash = self.compute_stop_hash(start_hash, commit_hashes,
                                               commit_indices, chunk_size)
            logger.debug('Computed stop hash: %s', stop_hash)

            log = self.list_commits(start_hash, stop_hash)
            log = log.strip('\n')
            if log == '':
                return

            log = log.strip('\n\x1e').split('\x1e')
            log = [row.strip().split('\x1f') for row in log]
            log = [[i.decode('utf-8', errors='ignore') for i in row]
                   for row in log]
            log = [dict(zip(GIT_COMMIT_FIELDS, row)) for row in log]
            commits = [Commit(i) for i in log]
            for c in commits:
                c.clean()

            signal.signal(signal.SIGALRM, alarm_handler)
            signal.alarm(5 * 60)  # 5 minutes

            try:
                self.add_stat_info(commits, start_hash, stop_hash,
                                   empty=(not include_diffstat))
                signal.alarm(0)
            except (AlarmError, OSError):
                logger.info('Could not obtain stat info within time limit')
                logger.info('Continuing without stats for commit range')

                if STAT_PROCESS:
                    pid = STAT_PROCESS.pid
                    STAT_PROCESS.terminate()
                    try:
                        os.kill(pid, 0)
                        STAT_PROCESS.kill()
                        logger.debug('Force-killed stat operation')
                    except OSError:
                        logger.debug('Gracefully terminated stat operation')

                    # Give the OS a few seconds to mark the memory as free
                    gc.collect()
                    time.sleep(10)

                self.add_stat_info(commits, start_hash, stop_hash, empty=True)

            start_hash = stop_hash
            yield commits

    def add_stat_info(self, commits, start_hash, stop_hash, empty=False):
        """
        Update each commit in place with stats about number of lines changed
        both in aggregate and per file.
        """
        log = self.list_stats(start_hash, stop_hash, empty)
        log = log.strip('\n')

        if log == '':
            return

        log = log.strip('\n\x1e').split('\x1e')
        log = [row.strip().split('\x1f') for row in log]
        stats_by_hash = {}
        regex = re.compile('^[a-z0-9]{40}$')

        for item in log:
            try:
                curr_hash, numstat = item[0].split('\n\n')
            except ValueError:
                curr_hash = item[0]
                numstat = ''

            if not re.match(regex, curr_hash):
                raise AssertionError('Hash did not match regex!')

            # Initialize the stat dictionary
            stats_by_hash[curr_hash] = {
                'lines_added': 0,
                'lines_deleted': 0,
                'lines_modified': 0,
                'lines_net': 0,
                'file_stats': None,
            }

            for file_stats in numstat.split('\n'):
                # A tag
                if file_stats == '':
                    continue

                if stats_by_hash[curr_hash]['file_stats'] is None:
                    stats_by_hash[curr_hash]['file_stats'] = []

                try:
                    plus, minus, filename = file_stats.split('\t')
                except ValueError:
                    # Files can have whitespace names - just ignore them
                    continue

                # Binary shows as '-'
                if plus == '-':
                    plus = 0

                if minus == '-':
                    minus = 0

                plus = int(plus)
                minus = int(minus)

                stats_by_hash[curr_hash]['file_stats'].append({
                    'filename': filename,
                    'lines_added': plus,
                    'lines_deleted': minus,
                    'lines_modified': plus + minus,
                    'lines_net': plus - minus,
                })
                stats_by_hash[curr_hash]['lines_added'] += plus
                stats_by_hash[curr_hash]['lines_deleted'] += minus
                stats_by_hash[curr_hash]['lines_modified'] += (plus + minus)
                stats_by_hash[curr_hash]['lines_net'] += (plus - minus)

        for commit in commits:
            obj = commit.commit
            obj.update(stats_by_hash[obj['commit_hash']])

        return None


class Commit(object):
    def __init__(self, commit):
        self.commit = commit

    @property
    def commit_hash(self):
        return self.commit['commit_hash']

    def clean(self):
        """Set the parent hash for a commit.

        Merge commits have two parents, so a decision must be made as to which
        parent to set as *the* parent. Since this script will be run on the
        branch that the user wishes to index, parent_hash is set to the commit
        that was made on this branch, which is the left-hand parent (index 0).

        Non-merge commits have one parent, so index 0 also covers this case
        correctly.
        """
        if self.commit.get('parent_hashes') != '':
            self.commit['parent_hashes'] = self.commit['parent_hashes'].split()
            self.commit['parent_hash'] = self.commit['parent_hashes'][0]
        else:
            # The root commit has no parent
            self.commit['parent_hashes'] = []
            self.commit['parent_hash'] = None


class Client(object):
    def _api_key_is_registered(self):
        data = {'api_key': self.api_key}
        try:
            send_request(API_KEY_REGISTRATION_URL, data=data, method='POST',
                         headers=self.headers)
            return True
        except urllib2.HTTPError as e:
            if e.code == 401 and e.server_response == \
                    'API key is not registered to an email address':
                return False
            else:
                raise

    def ensure_registered_account(self):
        if self._api_key_is_registered():
            return True, None

        logger.info(REGISTRATION_NOTICE)
        print()

        while True:
            registered, msg = self.prompt_for_account_registration()
            if registered:
                for line in msg.split('\n'):
                    logger.info(line)
                break
            else:
                for line in msg.split('\n'):
                    logger.error(line)

        return registered, msg

    def prompt_for_account_registration(self):
        email = raw_input('Email Address: ')
        password = getpass.getpass('Password: ')
        data = {'email_address': email, 'password': password,
                'api_key': self.api_key}
        try:
            res = send_request(SIGNUP_URL, data=data, method='POST',
                               headers=self.headers)
            return True, res['message']
        except urllib2.HTTPError as e:
            if e.code == 401:
                return False, e.server_response
            else:
                raise

    def _get_or_create_user_keys(self):
        config_file = os.path.expanduser(CONFIG_FILE)
        try:
            with open(config_file) as f:
                content = f.read().strip()
                if content == '':
                    raise IOError

                result = json.loads(content)

                if 'api_key' not in result:
                    raise Exception('Field api_key not set')
                else:
                    return False, result
        except ValueError:
            raise Exception('Config {} is not valid JSON'.format(config_file))
        except IOError:
            # No configuration file exists, so create a new account and
            # create the configuration file.
            response = send_request(SIGNUP_INIT_URL, method='POST')
            with open(config_file, 'wb') as f:
                result = {
                    'api_key': response['api_key'],
                    '_comment': CONFIG_FILE_COMMENT,
                }
                f.write(json.dumps(result, indent=4) + '\n')
                return True, result

    @property
    def api_key(self):
        return self._get_or_create_user_keys()[1]['api_key']

    @property
    def user_agent(self):
        user_agent = 'DiffStat.com Python Client %s [Python %s/%s]' % (
            SCRIPT_VERSION,
            platform.python_implementation(),
            platform.python_version()
        )
        return user_agent

    @property
    def headers(self):
        return {
            'User-Agent': self.user_agent,
            'Content-Type': 'application/json',
            'Accept': 'application/json',
            'Accept-Encoding': 'gzip,deflate',
            'Authorization': self.api_key,
            'X-Platform': platform.platform(),
            'X-Username': getpass.getuser(),
            'X-Client-MD5': get_file_md5(os.path.abspath(__file__)),
            'X-Git-Version': get_git_version(),
        }

    def get_last_head(self, repo):
        url = '{}?{}'.format(
            REPOSITORIES_URL,
            urllib.urlencode({'name': repo.get_name()}))
        response = send_request(url, headers=self.headers)
        last_head = response['last_head']
        logger.debug('Got last head for repository %s: %s', repo.get_name(),
                     last_head)
        return last_head

    def send_commit_chunk(self, repo, commits):
        data = {
            'repository_name': repo.get_name(),
            'repository_origin_url': repo.get_origin_url(),
            'commits': [i.commit for i in commits],
        }
        response = send_request(COMMITS_URL, data=data, method='POST',
                                headers=self.headers)
        return response

    def send_commits(self, repo, chunk_size):
        last_head = self.get_last_head(repo)

        if last_head:
            with ChDir(repo.repo_path):
                if not repo.commit_exists(last_head):
                    # Local history was over-written.
                    last_head = self.recover_repository(repo)

        commits_generator = repo.get_commit_objects(last_head, chunk_size)
        commits_sent = 0

        while True:
            try:
                try:
                    commits = commits_generator.next()
                except CommitHashNotFoundError:
                    chunk_size *= 2
                    return commits_sent + self.send_commits(repo, chunk_size)
                except EmptyRepositoryError:
                    return 0
            except StopIteration:
                if commits_sent:
                    logger.info('Done sending commit stats')
                else:
                    logger.info('No new commits so sending "sync" event')
                    self.send_commit_chunk(repo, [])
                    logger.info('Done sending "sync" event')
                break

            logger.info('Sending stats for %s new commits', len(commits))
            logger.info('Sending stats for commits %s through %s',
                        commits_sent + 1, commits_sent + len(commits))
            response = self.send_commit_chunk(repo, commits)
            logger.info('Server successfully received stats for %s commits',
                        len(response['commit_hashes']))
            commits_sent += len(commits)

        return commits_sent

    def get_commits(self, repo, sampling=1):
        url = '{}?{}'.format(COMMITS_URL, urllib.urlencode({
            'repository_name': repo.get_name(),
            'repository_origin_url': repo.get_origin_url(),
            'sampling': sampling,
        }))
        response = send_request(url, headers=self.headers)
        return response['commit_hashes']

    def set_last_head(self, repo, commit_hash):
        logger.info('Setting HEAD to %s', commit_hash)
        url = '{}?{}'.format(
            REPOSITORIES_URL,
            urllib.urlencode({'name': repo.get_name()}))

        data = {'last_head': commit_hash}
        response = send_request(url, data=data, method='PUT',
                                headers=self.headers)
        return response

    def recover_repository(self, repo):
        """Get the most recent local commit also found on the remote."""
        remote_commits = set(self.get_commits(repo, sampling=1000))
        local_commits_generator = repo.get_commit_objects()
        new_last_head = None

        # Iterate through local commits starting with the most recent to find
        # out what last_head can safely be set to on the server. In other words,
        # figure out how far back the client needs to look so that the server
        # can be sent the new commits and be up to date with the local checkout.
        while True:
            try:
                for i in reversed(local_commits_generator.next()):
                    if i.commit_hash in remote_commits:
                        new_last_head = i.commit_hash
                        break
            except StopIteration:
                break

        self.set_last_head(repo, new_last_head)
        return new_last_head

    def send_repository(self, repo):
        data = {
            'name': repo['sshUrl'],
            'origin_url': repo['sshUrl'],
            'is_private': repo['isPrivate'],
            'is_fork': repo['isFork'],
        }
        return send_request(REPOSITORIES_URL, data=data, method='POST',
                            headers=self.headers)


################################################################################
# GitHub API Wrapper

class GitHub(object):
    def __init__(self, github_token, identity_file):
        self.github_token = github_token
        self.identity_file = identity_file

    @property
    def user_agent(self):
        return self.get_user_login()

    @property
    def headers(self):
        return {
            'Accept': 'application/vnd.github.v3+json',
            'Authorization': 'Bearer {}'.format(self.github_token),
            'User-Agent': self.user_agent,
        }

    def send_graphql_query(self, query, variables):
        variables = json.dumps(variables)
        return send_request(GITHUB_GRAPHQL_URL,
                            data={'query': query, 'variables': variables},
                            method='POST',
                            headers=self.headers)

    def get_user_login(self):
        """Return the GitHub username of the user that owns this token."""
        url = GITHUB_API_URL + '/user'
        res = send_request(url, headers={
            'Accept': 'application/vnd.github.v3+json',
            'Authorization': 'Bearer {}'.format(self.github_token),
        })
        return res['login']

    def check_oauth_scopes(self):
        meta = send_request(GITHUB_API_URL, return_headers=True,
                            headers=self.headers)
        scopes = meta.getheader('X-OAuth-Scopes').replace(',', '').split()
        missing = []
        for item in REQUIRED_OAUTH_SCOPES:
            if item['scope'] not in scopes and item['parent'] not in scopes:
                missing.append(item['scope'])
        if missing:
            logger.critical('GitHub token missing required scopes: {}'.format(
                            ', '.join(missing)))
            logger.critical('Add missing scopes here: {}'.format(
                            GITHUB_TOKEN_URL))
            sys.exit(1)
        else:
            return True

    def get_organization(self, name):
        url = GITHUB_API_URL + '/orgs/{}'.format(name)
        return send_request(url, headers=self.headers)

    def user_exists(self, username):
        """
        If a GitHub user exists with this username, return True and the user.
        Else return False and None.
        """
        try:
            url = GITHUB_API_URL + '/users/{}'.format(username)
            res = send_request(url, headers=self.headers)
            return True, res
        except urllib2.HTTPError as e:
            if e.code == 404:
                return False, None
            else:
                raise

    def list_organizations(self):
        url = GITHUB_API_URL + '/user/orgs'
        try:
            return send_request(url, headers=self.headers)
        except urllib2.HTTPError as e:
            if e.code == 401:
                logger.critical('The GitHub token that you have provided is '
                                'invalid: {}'.format(self.github_token))
                sys.exit(1)
            else:
                raise

    def list_repositories(self, org_or_user):
        login = org_or_user['login']
        if org_or_user['type'].lower() == 'organization':
            return self.list_repositories_for_org(login)
        else:
            return self.list_repositories_for_user(login)

    def list_repositories_for_org(self, login, cursor=None, result=None):
        """Get all non-forked repositories owned by $login"""
        query = """
        query OrganizationRepositories($login:String!, $cursor:String) {
            organization(login: $login) {
                repositories(first: 100, affiliations:[OWNER],
                             after: $cursor) {
                    nodes {
                        name
                        description
                        isPrivate
                        isFork
                        url
                        sshUrl
                    }
                    pageInfo {
                        startCursor
                        endCursor
                    }
                }
            }
        }
        """
        variables = {'login': login, 'cursor': cursor}
        res = self.send_graphql_query(query, variables)
        nodes = res['data']['organization']['repositories']['nodes']
        repos = [i for i in nodes if not i['isFork']]
        if len(repos) == 0:
            if result is None:
                return []
            else:
                return result
        else:
            if result is None:
                result = repos
            else:
                result.extend(repos)
            cursor = (res['data']['organization']['repositories']
                         ['pageInfo']['endCursor'])
            return self.list_repositories_for_org(login, cursor, result)

    def list_repositories_for_user(self, login, cursor=None, result=None):
        """Get all non-forked repositories owned by $login"""
        query = """
        query UserRepositories($login:String!, $cursor:String) {
            user(login: $login) {
                repositories(first: 100, affiliations:[OWNER],
                             after: $cursor) {
                    nodes {
                        name
                        description
                        isPrivate
                        isFork
                        url
                        sshUrl
                    }
                    pageInfo {
                        startCursor
                        endCursor
                    }
                }
            }
        }
        """
        variables = {'login': login, 'cursor': cursor}
        res = self.send_graphql_query(query, variables)
        repos = res['data']['user']['repositories']['nodes']
        if len(repos) == 0:
            if result is None:
                return []
            else:
                return result
        else:
            if result is None:
                result = repos
            else:
                result.extend(repos)
            cursor = (res['data']['user']['repositories']
                         ['pageInfo']['endCursor'])
            return self.list_repositories_for_user(login, cursor, result)

    def sync_repositories(self, org, identity_file):
        repos = self.list_repositories(org)
        repos = filter(lambda r: not r['isFork'], repos)
        for repo in repos:
            clone = Clone(repo['sshUrl'], identity_file)
            clone.sync()

    def filter_orgs(self, server_orgs, command_line_orgs):
        """Filter out user-provided values that are not orgs or users."""
        if len(command_line_orgs):
            result = []
            by_key = {i['login'].lower(): i for i in server_orgs}

            for o in command_line_orgs:
                if o.lower() not in by_key:
                    # Not an org. Check if is a user
                    is_user, user = self.user_exists(o)
                    if is_user:
                        result.append(user)
                    else:
                        msg = 'No org or user found with name "%s"'
                        logger.warning(msg, o)
                else:
                    # Orgs returned from /user/$user/orgs do not have the same
                    # structure as the /orgs/$org call. The latter is closer
                    # to what the /users/$user call returns, so use it instead.
                    result.append(self.get_organization(o.lower()))
        else:
            # If no command-line orgs specified, just return all orgs
            # that the user belongs to.
            result = [self.get_organization(o['login'].lower()) for o in
                      server_orgs]

        return result


################################################################################
# Main

def parse_args(args):
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(title='subcommands',
                                       description='valid subcommands',
                                       help='additional help')

    # Parser for sync-commit-stats sub-command.
    sync_parser = subparsers.add_parser(
        'sync-commit-stats',
        description='Sync commit stats of local Git repositories with '
                    'DiffStat.com servers. \n\nSee link for more info: '
                    'https://www.diffstat.com/client-documentation',
        formatter_class=argparse.RawDescriptionHelpFormatter)
    sync_parser.set_defaults(subcommand='sync-commit-stats')
    sync_parser.add_argument('directory',
                             help='A directory that is a git repo, '
                                  'or which contains git repos in '
                                  'subdirectories',
                             nargs='+')
    sync_parser.add_argument('-v',
                             action='store_true',
                             dest='verbose',
                             help='Increase verbosity')

    # Parser for clone-github-repos sub-command.
    github_parser = subparsers.add_parser(
        'clone-github-repos',
        description='Clone remote GitHub repositories to the local filesystem.'
                    '\n\nSee link for more info: '
                    'https://www.diffstat.com/client-documentation',
        formatter_class=argparse.RawDescriptionHelpFormatter)
    github_parser.set_defaults(subcommand='clone-github-repos')
    github_parser.add_argument('directory',
                               help='Local directory where repositories will '
                                    'be cloned to')
    github_parser.add_argument('-i', dest='identity_file',
                               help='File from which the identity (private '
                                    'key) for public key SSH authentication is '
                                    'read. If not specified, default files '
                                    'located at ~/.ssh/id_rsa and '
                                    '~/.ssh/id_dsa are used.')
    github_parser.add_argument('-t', '--token', dest='token',
                               help='GitHub personal access token')
    github_parser.add_argument('-o', '--org', dest='organizations',
                               help='GitHub organizations that you are a '
                                    'member of (all if not specified)',
                               default=[],
                               action='append')
    github_parser.add_argument('-v', action='store_true', dest='verbose',
                               help='Increase verbosity')

    return parser.parse_args(args)


def main(args):
    # Parse arguments, initialize logging, and execute the appropriate
    # sub-command.
    parsed = parse_args(args)
    init_logger(parsed.verbose)

    if parsed.subcommand == 'sync-commit-stats':
        # Connect the API key with a web login by forcing account registration
        client = Client()
        client.ensure_registered_account()

        for dir_ in parsed.directory:
            tree = Tree(dir_)
            tree.sync_all_repositories()

        logger.info('Sync successful! Access your private reports here: '
                    '{}'.format(REPORTS_URL))

    elif parsed.subcommand == 'clone-github-repos':
        # Clone GitHub repositories to local disks, and tell DiffStat.com
        # servers about them.
        if parsed.token:
            github_token = parsed.token
        else:
            github_token = get_github_token()

        github = GitHub(github_token, parsed.identity_file)
        github.check_oauth_scopes()
        all_github_orgs = github.list_organizations()
        github_orgs_to_send = github.filter_orgs(
            all_github_orgs, parsed.organizations)

        client = Client()
        for org in github_orgs_to_send:
            repos = github.list_repositories(org)
            repos = filter(lambda r: not r['isFork'], repos)
            for repo in repos:
                client.send_repository(repo)

        # Clone/pull the latest code to the local filesystem
        with ChDir(parsed.directory):
            for org in github_orgs_to_send:
                github.sync_repositories(org, parsed.identity_file)

    return 0


if __name__ == '__main__':
    try:
        sys.exit(main(sys.argv[1:]))
    except KeyboardInterrupt:
        try:
            print()
            sys.exit(0)
        except SystemExit:
            print()
            os._exit(0)
