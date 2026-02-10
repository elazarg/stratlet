"""
Windows Job Object helpers for child-process lifetime management.

When assigned to a Job Object with JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE,
all child processes are automatically killed when the job handle is closed
(i.e. when the daemon process exits for any reason — crash, OOM, hard kill).

On non-Windows platforms, all functions degrade gracefully (return None/False).
Uses only ctypes (stdlib) — no external dependencies.
"""

import sys

if sys.platform == "win32":
    import ctypes
    from ctypes import wintypes

    kernel32 = ctypes.windll.kernel32

    # Job Object constants
    JobObjectExtendedLimitInformation = 9
    JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE = 0x2000

    class IO_COUNTERS(ctypes.Structure):
        _fields_ = [
            ("ReadOperationCount", ctypes.c_ulonglong),
            ("WriteOperationCount", ctypes.c_ulonglong),
            ("OtherOperationCount", ctypes.c_ulonglong),
            ("ReadTransferCount", ctypes.c_ulonglong),
            ("WriteTransferCount", ctypes.c_ulonglong),
            ("OtherTransferCount", ctypes.c_ulonglong),
        ]

    class JOBOBJECT_BASIC_LIMIT_INFORMATION(ctypes.Structure):
        _fields_ = [
            ("PerProcessUserTimeLimit", ctypes.c_longlong),
            ("PerJobUserTimeLimit", ctypes.c_longlong),
            ("LimitFlags", wintypes.DWORD),
            ("MinimumWorkingSetSize", ctypes.c_size_t),
            ("MaximumWorkingSetSize", ctypes.c_size_t),
            ("ActiveProcessLimit", wintypes.DWORD),
            ("Affinity", ctypes.POINTER(ctypes.c_ulong)),
            ("PriorityClass", wintypes.DWORD),
            ("SchedulingClass", wintypes.DWORD),
        ]

    class JOBOBJECT_EXTENDED_LIMIT_INFORMATION(ctypes.Structure):
        _fields_ = [
            ("BasicLimitInformation", JOBOBJECT_BASIC_LIMIT_INFORMATION),
            ("IoInfo", IO_COUNTERS),
            ("ProcessMemoryLimit", ctypes.c_size_t),
            ("JobMemoryLimit", ctypes.c_size_t),
            ("PeakProcessMemoryUsed", ctypes.c_size_t),
            ("PeakJobMemoryUsed", ctypes.c_size_t),
        ]


def create_kill_on_close_job():
    """Create a Windows Job Object with KILL_ON_JOB_CLOSE.

    Returns the job handle (int) on success, None on failure or non-Windows.
    """
    if sys.platform != "win32":
        return None

    try:
        handle = kernel32.CreateJobObjectW(None, None)
        if not handle:
            return None

        info = JOBOBJECT_EXTENDED_LIMIT_INFORMATION()
        info.BasicLimitInformation.LimitFlags = JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE

        ok = kernel32.SetInformationJobObject(
            handle,
            JobObjectExtendedLimitInformation,
            ctypes.byref(info),
            ctypes.sizeof(info),
        )
        if not ok:
            kernel32.CloseHandle(handle)
            return None

        return handle
    except Exception:
        return None


def assign_process(job_handle, process_handle) -> bool:
    """Assign a process to a Job Object.

    Args:
        job_handle: Handle from create_kill_on_close_job()
        process_handle: subprocess.Popen._handle (Windows process handle)

    Returns True on success, False on failure or non-Windows.
    """
    if sys.platform != "win32" or job_handle is None:
        return False

    try:
        # Popen._handle is a subprocess.Handle; int() gives the raw HANDLE value
        raw_handle = int(process_handle)
        return bool(kernel32.AssignProcessToJobObject(job_handle, raw_handle))
    except Exception:
        return False


def close_job(job_handle):
    """Close a Job Object handle.

    On close, if KILL_ON_JOB_CLOSE was set, all assigned processes are killed.
    Safe to call with None.
    """
    if sys.platform != "win32" or job_handle is None:
        return

    try:
        kernel32.CloseHandle(job_handle)
    except Exception:
        pass
