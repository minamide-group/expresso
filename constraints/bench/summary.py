# 戦略 thesis のログ出力を要約する
from collections import namedtuple
import re
import datetime as dt
import sys

Line = namedtuple('Line', ['line', 'date', 'time', 'name', 'message'])

def parseLine(line):
    m = re.match('(\d{2}-\d{2}) (\S*) (\S*) - (.*)', line)
    if m is None:
        print(line)
    return Line(
        line=m.group(0),
        date=m.group(1),
        time=parseTime(m.group(2)),
        name=m.group(3),
        message=m.group(4)
    )

def parseTime(time):
    return dt.datetime.strptime(time, '%H:%M:%S.%f')

# (|Q|, |X|, |D|)
def parseSize(size):
    m = re.match('\((\d+),(\d+),(\d+),(\d+),(\d+),(\d+)\)', size)
    return (int(m.group(1)), int(m.group(2)), int(m.group(4)))

def summarize(lines):
    parsed = [parseLine(line) for line in lines]
    class TimeRegistrar:
        def __init__(self):
            self.time = None
        def setTime(self, time):
            self.time = time
    time = TimeRegistrar()
    res = {}
    def registerTime(newTime, name):
        if time.time is not None:
            res[name] = (newTime - time.time) // dt.timedelta(microseconds=1000)
        time.setTime(newTime)
    res['name'] = parsed[0].name
    assert(re.match('start compilation', parsed[0].message) is not None)
    registerTime(parsed[0].time, '') # start compilation
    while re.match('composition done', parsed[1].message) is None:
        parsed = parsed[1:]
    res['size1'] = parseSize(re.match('compose (.*) and', parsed[0].message).group(1))
    res['size2'] = parseSize(re.match('composition done, got PSST (.*)', parsed[1].message).group(1))
    registerTime(parsed[1].time, 'comp') # composition done
    registerTime(parsed[2].time, 'check') # checking done
    if len(parsed) == 4:
        registerTime(parsed[3].time, 'model')
    return res

if __name__ == '__main__':
    lines = sys.stdin.readlines()
    summary = summarize([line for line in lines if line != ''])
    print(summary)
    # re.
