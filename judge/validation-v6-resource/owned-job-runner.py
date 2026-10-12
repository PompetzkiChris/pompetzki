"""Launch only a newly created suspended child inside a memory-limited Windows Job."""
import ctypes as C
from ctypes import wintypes as W
import hashlib, json, pathlib, subprocess, time

k = C.WinDLL('kernel32', use_last_error=True)
SIZE_T = C.c_size_t

class SECURITY_ATTRIBUTES(C.Structure):
    _fields_ = [('nLength', W.DWORD), ('lpSecurityDescriptor', W.LPVOID), ('bInheritHandle', W.BOOL)]
class STARTUPINFO(C.Structure):
    _fields_ = [('cb', W.DWORD), ('lpReserved', W.LPWSTR), ('lpDesktop', W.LPWSTR), ('lpTitle', W.LPWSTR), ('dwX', W.DWORD), ('dwY', W.DWORD), ('dwXSize', W.DWORD), ('dwYSize', W.DWORD), ('dwXCountChars', W.DWORD), ('dwYCountChars', W.DWORD), ('dwFillAttribute', W.DWORD), ('dwFlags', W.DWORD), ('wShowWindow', W.WORD), ('cbReserved2', W.WORD), ('lpReserved2', C.POINTER(W.BYTE)), ('hStdInput', W.HANDLE), ('hStdOutput', W.HANDLE), ('hStdError', W.HANDLE)]
class PROCESS_INFORMATION(C.Structure):
    _fields_ = [('hProcess', W.HANDLE), ('hThread', W.HANDLE), ('dwProcessId', W.DWORD), ('dwThreadId', W.DWORD)]
class BASIC_LIMITS(C.Structure):
    _fields_ = [('PerProcessUserTimeLimit', C.c_int64), ('PerJobUserTimeLimit', C.c_int64), ('LimitFlags', W.DWORD), ('MinimumWorkingSetSize', SIZE_T), ('MaximumWorkingSetSize', SIZE_T), ('ActiveProcessLimit', W.DWORD), ('Affinity', SIZE_T), ('PriorityClass', W.DWORD), ('SchedulingClass', W.DWORD)]
class IO_COUNTERS(C.Structure):
    _fields_ = [(name, C.c_uint64) for name in ('ReadOperationCount', 'WriteOperationCount', 'OtherOperationCount', 'ReadTransferCount', 'WriteTransferCount', 'OtherTransferCount')]
class EXTENDED_LIMITS(C.Structure):
    _fields_ = [('BasicLimitInformation', BASIC_LIMITS), ('IoInfo', IO_COUNTERS), ('ProcessMemoryLimit', SIZE_T), ('JobMemoryLimit', SIZE_T), ('PeakProcessMemoryUsed', SIZE_T), ('PeakJobMemoryUsed', SIZE_T)]

k.CreateJobObjectW.argtypes = [W.LPVOID, W.LPCWSTR]; k.CreateJobObjectW.restype = W.HANDLE
k.SetInformationJobObject.argtypes = [W.HANDLE, C.c_int, W.LPVOID, W.DWORD]; k.SetInformationJobObject.restype = W.BOOL
k.QueryInformationJobObject.argtypes = [W.HANDLE, C.c_int, W.LPVOID, W.DWORD, C.POINTER(W.DWORD)]; k.QueryInformationJobObject.restype = W.BOOL
k.AssignProcessToJobObject.argtypes = [W.HANDLE, W.HANDLE]; k.AssignProcessToJobObject.restype = W.BOOL
k.TerminateJobObject.argtypes = [W.HANDLE, W.UINT]; k.TerminateJobObject.restype = W.BOOL
k.CreateFileW.argtypes = [W.LPCWSTR, W.DWORD, W.DWORD, C.POINTER(SECURITY_ATTRIBUTES), W.DWORD, W.DWORD, W.HANDLE]; k.CreateFileW.restype = W.HANDLE
k.CreateProcessW.argtypes = [W.LPCWSTR, W.LPWSTR, W.LPVOID, W.LPVOID, W.BOOL, W.DWORD, W.LPVOID, W.LPCWSTR, C.POINTER(STARTUPINFO), C.POINTER(PROCESS_INFORMATION)]; k.CreateProcessW.restype = W.BOOL
k.ResumeThread.argtypes = [W.HANDLE]; k.ResumeThread.restype = W.DWORD
k.WaitForSingleObject.argtypes = [W.HANDLE, W.DWORD]; k.WaitForSingleObject.restype = W.DWORD
k.GetExitCodeProcess.argtypes = [W.HANDLE, C.POINTER(W.DWORD)]; k.GetExitCodeProcess.restype = W.BOOL
k.TerminateProcess.argtypes = [W.HANDLE, W.UINT]; k.TerminateProcess.restype = W.BOOL
k.CloseHandle.argtypes = [W.HANDLE]; k.CloseHandle.restype = W.BOOL

def checked(value, operation):
    if not value:
        raise C.WinError(C.get_last_error(), operation)
    return value

def run_owned(argv, output, stem, memory_mib=256, timeout_seconds=30, cwd=None):
    output = pathlib.Path(output)
    assert output.is_dir()
    executable = pathlib.Path(argv[0]).resolve(strict=True)
    assert executable.is_file()
    argv = [str(executable), *map(str, argv[1:])]
    handles, job, pi = [], None, PROCESS_INFORMATION()
    started = time.perf_counter()
    stdout_path, stderr_path = output / (stem + '.stdout.txt'), output / (stem + '.stderr.txt')
    result = {'command': argv, 'memory_limit_bytes': memory_mib * 1024 * 1024, 'timeout_seconds': timeout_seconds, 'created_suspended': False, 'assigned_to_job_before_resume': False, 'kill_on_job_close': True, 'owned_output_files_create_new': True}
    try:
        job = checked(k.CreateJobObjectW(None, None), 'CreateJobObjectW')
        limits = EXTENDED_LIMITS()
        limits.BasicLimitInformation.LimitFlags = 0x100 | 0x2000
        limits.ProcessMemoryLimit = result['memory_limit_bytes']
        checked(k.SetInformationJobObject(job, 9, C.byref(limits), C.sizeof(limits)), 'SetInformationJobObject')
        sa = SECURITY_ATTRIBUTES(C.sizeof(SECURITY_ATTRIBUTES), None, True)
        for path, access, disposition in ((stdout_path, 0x40000000, 1), (stderr_path, 0x40000000, 1), ('NUL', 0x80000000, 3)):
            handle = k.CreateFileW(str(path), access, 3, C.byref(sa), disposition, 0x80, None)
            if handle == C.c_void_p(-1).value:
                raise C.WinError(C.get_last_error(), 'CreateFileW')
            handles.append(handle)
        startup = STARTUPINFO()
        startup.cb, startup.dwFlags = C.sizeof(startup), 0x100
        startup.hStdOutput, startup.hStdError, startup.hStdInput = handles
        command = C.create_unicode_buffer(subprocess.list2cmdline(argv))
        checked(k.CreateProcessW(str(executable), command, None, None, True, 0x4 | 0x08000000, None, str(cwd) if cwd else None, C.byref(startup), C.byref(pi)), 'CreateProcessW')
        result.update({'created_suspended': True, 'owned_child_pid': pi.dwProcessId})
        if not k.AssignProcessToJobObject(job, pi.hProcess):
            error = C.get_last_error()
            k.TerminateProcess(pi.hProcess, 0xF001)
            k.WaitForSingleObject(pi.hProcess, 5000)
            raise C.WinError(error, 'AssignProcessToJobObject: owned suspended child terminated')
        result['assigned_to_job_before_resume'] = True
        if k.ResumeThread(pi.hThread) == 0xFFFFFFFF:
            raise C.WinError(C.get_last_error(), 'ResumeThread')
        wait = k.WaitForSingleObject(pi.hProcess, int(timeout_seconds * 1000))
        result['timeout'] = wait == 0x102
        if result['timeout']:
            checked(k.TerminateJobObject(job, 0xF002), 'TerminateJobObject timeout')
            checked(k.WaitForSingleObject(pi.hProcess, 5000) == 0, 'WaitForSingleObject terminated child')
        elif wait != 0:
            raise C.WinError(C.get_last_error(), 'WaitForSingleObject')
        exit_code = W.DWORD()
        checked(k.GetExitCodeProcess(pi.hProcess, C.byref(exit_code)), 'GetExitCodeProcess')
        peaks = EXTENDED_LIMITS()
        checked(k.QueryInformationJobObject(job, 9, C.byref(peaks), C.sizeof(peaks), None), 'QueryInformationJobObject')
        result.update({'exit_code': exit_code.value, 'peak_process_memory_bytes': peaks.PeakProcessMemoryUsed, 'seconds': round(time.perf_counter() - started, 6)})
    finally:
        if job:
            k.CloseHandle(job)
        elif pi.hProcess:
            k.TerminateProcess(pi.hProcess, 0xF003)
        for handle in (pi.hThread, pi.hProcess, *handles):
            if handle:
                k.CloseHandle(handle)
    stdout, stderr = stdout_path.read_bytes(), stderr_path.read_bytes()
    result.update({'stdout_file': stdout_path.name, 'stderr_file': stderr_path.name, 'stdout_sha256': hashlib.sha256(stdout).hexdigest(), 'stderr_sha256': hashlib.sha256(stderr).hexdigest(), 'stdout': stdout.decode('utf-8', errors='replace'), 'stderr': stderr.decode('utf-8', errors='replace')})
    (output / (stem + '.result.json')).write_text(json.dumps(result, indent=2) + '\n')
    return result
